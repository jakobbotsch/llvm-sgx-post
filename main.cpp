#include <stdio.h>
#include <string.h>
#include <gelf.h>
#include <err.h>
#include <utility>
#include <cstdint>
#include <vector>
#include <limits>
#include <algorithm>
#include <memory>
#include <unistd.h>
#include <syscall.h>
#include <linux/random.h>

template <class Fun>
class ScopeGuard {
    Fun _f;
    bool _active;
public:
    ScopeGuard(Fun f)
        : _f(std::move(f))
        , _active(true)
    {
    }
    ~ScopeGuard() { _f(); }

    ScopeGuard() = delete;
    ScopeGuard(const ScopeGuard&) = delete;
    ScopeGuard& operator=(const ScopeGuard&) = delete;
    ScopeGuard(ScopeGuard&& rhs)
        : _f(std::move(rhs._f))
        , _active(rhs._active)
    {
        rhs._active = false;
    }
};

template <class Fun>
ScopeGuard<Fun> scopeGuard(Fun f)
{
    return ScopeGuard<Fun>(std::move(f));
}

struct Region
{
    uint32_t Offset;
    uint32_t Size;
};

struct EnclaveData
{
    bool Encrypted;
    uint32_t CryptoKey[4];
    Region EncryptedRegions[32];
};

bool lookupSymbol(Elf *elf, const char *name, GElf_Sym *sym);
std::vector<Region> getRegionsToEncrypt(Elf *elf, Elf_Scn *&sgxtext);
void encryptAndFillData(FILE *file, Elf *elf, Elf_Scn *sgxtext,
                        std::vector<Region>& encryptedRegions);

int main(int argc, char *argv[])
{
    const char *filePath = argv[1];
    if (argc < 2)
        errx(1, "Must specify an llvm-sgx compiled ELF image");

    printf("Processing '%s'\n", filePath);

    if (elf_version(EV_CURRENT) == EV_NONE)
        errx(2, "Could not initialize libelf: %s", elf_errmsg(-1));

    FILE *file = fopen(filePath, "r+b");
    if (file == nullptr)
        errx(3, "Could not open '%s'", filePath);

    auto g1 = scopeGuard([&] { fclose(file); });

    Elf *elf = elf_begin(fileno(file), ELF_C_READ, nullptr);
    if (elf == nullptr)
        errx(4, "Could not open '%s' as an ELF file", filePath);

    auto g2 = scopeGuard([&] { elf_end(elf); });

    if (elf_kind(elf) != ELF_K_ELF)
        errx(5, "'%s' is not an ELF file", filePath);

    int elfClass = gelf_getclass(elf);
    if (gelf_getclass(elf) != ELFCLASS64)
        errx(6, "ELF is not a 64-bit ELF file (got class %d)", elfClass);

    size_t sectionHeaderStringTableIndex;
    if (elf_getshdrstrndx(elf, &sectionHeaderStringTableIndex) != 0)
        errx(7, "Failed to get section header string table index: %s", elf_errmsg(-1));

    Elf_Scn *sgxtext;
    std::vector<Region> encryptedRegions = getRegionsToEncrypt(elf, sgxtext);

    encryptAndFillData(file, elf, sgxtext, encryptedRegions);

    return 0;
}

std::vector<Region> getRegionsToEncrypt(Elf *elf, Elf_Scn *&sgxtext)
{
    std::vector<Region> unencryptedRegions;
    GElf_Shdr shdr;
    for (const char* unencryptedSym : {"__llvmsgx_enclave_entry", "__llvmsgx_enclave_data"})
    {
        GElf_Sym sym;
        if (!lookupSymbol(elf, unencryptedSym, &sym))
            errx(8, "Could not find symbol '%s'\n", unencryptedSym);

        // Value is the virtual address here, so get relative offset in section.
        sgxtext = elf_getscn(elf, sym.st_shndx);
        if (sgxtext == nullptr || gelf_getshdr(sgxtext, &shdr) != &shdr)
            errx(9, "Could not get section for symbol: %s", elf_errmsg(-1));

        uint64_t offset = sym.st_value - shdr.sh_addr;
        if (offset > std::numeric_limits<uint32_t>::max() ||
            sym.st_size > std::numeric_limits<uint32_t>::max())
        {
            errx(10, "Overflow in offset or size of symbol %s. Offset: %lx. Size: %lx\n",
                 unencryptedSym, offset, sym.st_size);
        }

        unencryptedRegions.push_back(Region { static_cast<uint32_t>(offset),
                                              static_cast<uint32_t>(sym.st_size) });
    }

    std::sort(unencryptedRegions.begin(), unencryptedRegions.end(),
              [](Region& a, Region& b) { return a.Offset < b.Offset; });

    std::vector<Region> encryptedRegions;
    uint32_t curStart = 0;
    // Take complement of unencrypted region
    auto commitRegion = [&](uint32_t end)
    {
        if (end > curStart)
            encryptedRegions.push_back(Region { curStart, end - curStart });
    };

    for (const Region& unenc : unencryptedRegions)
    {
        commitRegion(unenc.Offset);
        curStart = unenc.Offset + unenc.Size;
    }

    commitRegion(shdr.sh_size);
    return encryptedRegions;
}

bool lookupSymbol(Elf *elf, const char *name, GElf_Sym *sym)
{
    Elf_Scn *scn = nullptr;
    while ((scn = elf_nextscn(elf, scn)) != nullptr)
    {
        GElf_Shdr shdr;
        if (gelf_getshdr(scn, &shdr) != &shdr)
            errx(11, "getshdr failed: %s", elf_errmsg(-1));

        if (shdr.sh_type != SHT_SYMTAB)
            continue;

        Elf_Data *data = elf_getdata(scn, nullptr);
        if (data == nullptr || data->d_type != ELF_T_SYM)
            continue;

        for (int i = 0;; i++)
        {
            if (gelf_getsym(data, i, sym) != sym)
                break;

            const char *symName = elf_strptr(elf, shdr.sh_link, sym->st_name);
            if (strcmp(symName, name) == 0)
                return true;
        }
    }

    return false;
}

static void xtea_encrypt(uint32_t v[2], uint32_t const k[4])
{
    unsigned int i;
    uint32_t v0=v[0], v1=v[1], sum=0, delta=0x9E3779B9;
    for (i=0; i < 32; i++) {
        v0 += (((v1 << 4) ^ (v1 >> 5)) + v1) ^ (sum + k[sum & 3]);
        sum += delta;
        v1 += (((v0 << 4) ^ (v0 >> 5)) + v0) ^ (sum + k[(sum>>11) & 3]);
    }
    v[0]=v0; v[1]=v1;
}

void encryptAndFillData(FILE *file, Elf *elf, Elf_Scn *sgxtext,
                        std::vector<Region>& encryptedRegions)
{
    GElf_Shdr shdr;
    if (gelf_getshdr(sgxtext, &shdr) != &shdr)
        errx(12, "Could not get shdr for sgxtext: %s", elf_errmsg(-1));

    std::vector<uint8_t> sgxtextData(shdr.sh_size);

    if (fseek(file, shdr.sh_offset, SEEK_SET) != 0)
        errx(13, "fseek failed while trying to read sgxtext");

    if (fread(sgxtextData.data(), 1, shdr.sh_size, file) != shdr.sh_size)
        errx(14, "Failed to read data of sgxtext");

    uint32_t key[4];
    while (syscall(SYS_getrandom, key, sizeof(key), 0) != sizeof(key))
    {
        if (errno == EINTR)
            continue;

        errx(15, "getrandom failed");
    }

    // Now encrypt the data using XTEA in counter mode.
    uint64_t counter = 0;
    uint32_t cipherStream[2];
    int cipherIndex = 8;
    for (const Region& reg : encryptedRegions)
    {
        for (uint32_t i = 0; i < reg.Size; i++)
        {
            if (cipherIndex == 8)
            {
                memcpy(cipherStream, &counter, 8);
                xtea_encrypt(cipherStream, key);
                counter++;
                cipherIndex = 0;
            }

            sgxtextData[reg.Offset + i] ^= ((char*)cipherStream)[cipherIndex++];
        }
    }

    // Write information to be used by binary
    GElf_Sym encDataSym;
    if (!lookupSymbol(elf, "__llvmsgx_enclave_data", &encDataSym))
        errx(16, "Could not get enclave data symbol");

    EnclaveData encData = {0};
    encData.Encrypted = true;

    std::copy(std::begin(key), std::end(key), encData.CryptoKey);

    const int maxNumEncRegions =
        sizeof(encData.EncryptedRegions) / sizeof(encData.EncryptedRegions[0]);
    if (encryptedRegions.size() > maxNumEncRegions)
    {
        errx(17, "Too many regions: %zu vs %d supported\n",
             encryptedRegions.size(), maxNumEncRegions);
    }

    std::copy(encryptedRegions.begin(), encryptedRegions.end(),
              encData.EncryptedRegions);

    memcpy(&sgxtextData[encDataSym.st_value - shdr.sh_addr], &encData, sizeof(encData));

    if (fseek(file, shdr.sh_offset, SEEK_SET) != 0)
        errx(18, "fseek failed while trying to write sgxtext");

    if (fwrite(sgxtextData.data(), 1, sgxtextData.size(), file) != sgxtextData.size())
        errx(19, "Could not write processed file back");
}
