/*
WATL Exercise
Version: 0 (AS INTENDED)

Vendor OS & Compiler: Windows 11, MSVC
*/

#pragma region Debug

#if !defined(BUILD_DEBUG)
#define debug_trap()
#define assert(cond)
#define assert_msg(cond, msg, ...)
#endif

#if defined(BUILD_DEBUG)
#define debug_trap() __debugbreak()

#define assert(cond) assert_msg(cond, nullptr)
#define assert_msg(cond, msg, ...)                                                                                   \
do                                                                                                                   \
{                                                                                                                    \
	if (! (cond))                                                                                                    \
	{                                                                                                                \
		assert_handler(lit(stringify(cond)), lit(__FILE__), lit(__func__), cast(S64, __LINE__), msg, ##__VA_ARGS__); \
		debug_trap();                                                                                                \
	}                                                                                                                \
}                                                                                                                    \
while(0)
#endif

void assert_handler(Str8 condition, Str8 path_file, Str8 function, S64 line, message, ...);

#pragma endregion Debug

#pragma region C Things

#define cast(type, data)  ((type)(data))
#define pcast(type, data) * cast(type*, & (data))

#define nullptr cast(void*, 0)

#define glue_impl(A, B) A ## B
#define glue(A, B)      glue_impl(A, B)

// Enforces size querying uses SSIZE type.
#define size_of(data) cast(SSIZE, sizeof(data))

#define stringify_(S) #S
#define stringify(S)  stringify_(S)

#define typeof __typeof__

#include <intrin.h>
#include <tmmintrin.h>
#include <wmmintrin.h>

#define KILO(n) (cast(USIZE, n) << 10)
#define MEGA(n) (cast(USIZE, n) << 20)
#define GIGA(n) (cast(USIZE, n) << 30)
#define TERA(n) (cast(USIZE, n) << 40)

typedef unsigned __int8  U8;
typedef signed   __int8  S8;
typedef unsigned __int16 U16;
typedef signed   __int16 S16;
typedef unsigned __int32 U32;
typedef signed   __int32 S32;
typedef unsigned __int64 U64;
typedef signed   __int64 S64;

typedef size_t    USIZE;
typedef ptrdiff_t SSIZE;

enum {
	false,
	true,
	true_overflow,
};
typedef S8  B8;
typedef S16 B16;
typedef S32 B32;

#pragma region C Things

#pragma region Memory Operations

inline
void* memory_copy(void* restrict dest, void const* restrict src, USIZE length)
{
	if (dest == nullptr || src == nullptr || length == 0) {
		return nullptr;
	}
	// https://learn.microsoft.com/en-us/cpp/intrinsics/movsb?view=msvc-170
	__movsb((unsigned char*)dest, (const unsigned char*)src, length);
	return dest;
}

inline 
B32 memory_zero(void* dest, USIZE length)
{
	if (dest == nullptr || length <= 0) {
		return false;
	}
	__stosb((unsigned char*)dest, 0, length);
	return true;
}

typedef struct Slice_Byte Slice_Byte;
struct Slice_Byte {
	U8*   ptr;
	USIZE len;
};

#define slice_assert(slice) do {  \
	assert(slice.ptr != nullptr); \
	assert(slice.len > 0);        \
} while(0)

inline
void slice__copy(Slice_Byte dest, SSIZE dest_typewidth, Slice_Byte src, SSIZE src_typewidth) {
	assert(dest.len >= src.len);
	slice_assert(dest);
	slice_assert(src);
	memory_copy(dest.ptr, src.ptr, src.len);
}

#define slice_copy(dest, src) slice__copy(                                            \
	(Slice_Byte){(dest).ptr, (dest).len * size_of(*(dest).ptr)}, size_of(*(dest).ptr) \
,	(Slice_Byte){(src ).ptr, (src ).len * size_of(*(src ).ptr)}, size_of(*(src ).ptr) \
)

#pragma endregion Memory Operations

#pragma region Allocator Interface

typedef U32 AllocatorOp; enum {
	Alloc,
	Alloc_NoZero, // If Alloc exist, so must No_Zero
	Free,
	Reset,
	Resize,
	Resize_NoZero,
	Rewind,
	SavePoint,
	Query, // Must always be implemented
};

/*
These are good to enforce constraints via asserts,
however for situations that have hard constraints, 
it may be better to enforce strict allocator type/s for the receiving data structure or code path.
*/
typedef U64 AllocatorQueryFlags; enum {
	AllocatorQuery_Alloc        = (1 << 0),
	AllocatorQuery_Free         = (1 << 1),
	// Wipe the allocator's state
	AllocatorQuery_Reset        = (1 << 2), 
	// Supports both grow and shrink
	AllocatorQuery_Resize       = (1 << 3), 
	AllocatorQuery_ResizeShrink = (1 << 4),
	AllocatorQuery_ResizeGrow   = (1 << 5),	
	// Ability to rewind to a save point (ex: arenas, stack), must also be able to save such a point
	AllocatorQuery_Rewind       = (1 << 6), 
};

typedef struct AllocatorOpData AllocatorOpData;
struct AllocatorProcIn {
	void*        data;
	AllocatorOp  op;
	SSIZE        requested_size;
	SSIZE        alignment;
	Slice_Byte   old_allocation;
};
typedef struct AllocatorProc_Out AllocatorProc_Out;
struct AllocatorProc_Out {
	Slice_Byte          allocation;
	AllocatorQueryFlags features;
	SSIZE               left;
	SSIZE               max_alloc;
	SSIZE               min_alloc;
	B32                 continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
};
typedef void (AllocatorProc) (AllocatorOpData In, AllocatorOpData* Out);

typedef struct AllocatorInfo AllocatorInfo;
struct AllocatorInfo {
	AllocatorProc proc;
	void*         data;
};

// This the point right after the last allocation usually.
typedef struct AllocatorSP AllocatorSP;
struct AllocatorSP {
	USIZE slot;
};

#define MEMORY_ALIGNMENT_DEFAULT 2 * size_of(void*))

AllocatorQueryFlags allocator_query(AllocatorInfo ainfo);

Slice_Byte  mem_alloc          (AllocatorInfo ainfo, SSIZE size);
Slice_Byte  mem_alloc_nz       (AllocatorInfo ainfo, SSIZE size);
Slice_Byte  mem_alloc_align    (AllocatorInfo ainfo, SSIZE size);
Slice_Byte  mem_alloc_align_nz (AllocatorInfo ainfo, SSIZE size);
void        mem_free           (AllocatorInfo ainfo, SliceByte mem);
void        mem_reset          (AllocatorInfo ainfo);
Slice_Byte  mem_grow           (AllocatorInfo ainfo, SliceByte mem, SSIZE size);
Slice_Byte  mem_shrink         (AllocatorInfo ainfo, SliceByte mem, SSIZE size);
Slice_Byte  mem_resize         (AllocatorInfo ainfo, SliceByte mem, SSIZE desired_size);
Slice_Byte  mem_resize_nz      (AllocatorInfo ainfo, SliceByte mem, SSIZE desired_size);
Slice_Byte  mem_resize_align   (AllocatorInfo ainfo, SliceByte mem, SSIZE desired_size, SSIZE alignment);
Slice_Byte  mem_resize_align_nz(AllocatorInfo ainfo, SliceByte mem, SSIZE desired_size, SSIZE alignment);
void        mem_rewind         (AllocatorInfo ainfo, AllocatorSP save_point);
AllocatorSP mem_save_point     (AllocatorInfo ainfo);

#pragma endregion Allocator Interface

#pragma region Strings

typedef unsigned char UTF8;
typedef struct Str8 Str8;
struct Str8 {
	UTF8* ptr;
	SSIZE len;
};
#define lit(string_literal) (Str8){ string_literal, size_of(string_literal) - 1 }

typedef struct Str8Cache_Slot Str8Cache_Slot;
struct Str8Cache_Slot {
	Str8Cache_Slot* next;
	Str8 value;
	U64  key;
	B32  occupied;
};

typedef struct Slice_Str8Cache_Slot Slice_Str8Cache_Slot;
struct Slice_Str8Cache_Slot {
	Str8Cache_Slot* ptr;
	SSIZE           len;
};

typedef struct Str8Cache Str8Cache;
struct Str8Cache {
	AllocatorInfo        ainfo_str;
	AllocatorInfo        ainfo_slots;
	Slice_Str8Cache_Slot table;
};

void      str8cache_init(Str8Cache* cache, AllocatorInfo ainfo_str, AllocatorInfo ainfo_slots);
Str8Cache str8cache_make(                  AllocatorInfo ainfo_str, AllocatorInfo ainfo_slots);



#pragma endregion Strings

#pragma region File System

typedef struct FileOpInfo;
struct FileOpInfo {
	Slice_Byte content;
};

struct Opts_read_file_contents {
	AllocatorInfo backing;
	B32           zero_backing;
}

void file_read_contents_api(FileOpInfo* result, Str8 path, Opts_read_file_contents opts);
void file_write_str8       (Str8 path, Str8 content);

FileOpInfo file_read_contents(Str8 path, Opts_read_file_contents* opts);
#define file_read_contents(path, ...) file__read_contents(path, &(Opts_read_file_contents){__VA_ARGS__})

#pragma endregion File System

#pragma region WATL

typedef struct WATL_Tok WATL_Tok;
struct WATL_Tok {
	UTF8* code;
};

typedef struct Slice_WATL_LexMsg Slice_WATL_LexMsg;
struct Slice_WATL_LexMsg {
	WATL_LexMsg* ptr;
	SSIZE        len;
};

typedef struct Slice_WATL_Tok Slice_WATL_Tok;
struct Slice_WATL_Tok {
	WATL_Tok* ptr;
	SSIZE     len;
};

typedef U32 WATL_LexStatus; enum {
	WATL_LexStatus_MemFail_Alloc,
	WATL_LexStatus_MemFail_SliceConstraintFail,
	WATL_LexStatus_PosUntrackable,
	WATL_LexStatus_UnsupportedCodepoints,
	WATL_LexStatus_MessageOverflow,
};

typedef struct WATL_Pos WATL_Pos;
struct WATL_Pos {
	S32 line;
	S32 column;
};

typedef struct WATL_LexMsg WATL_LexMsg;
struct WATL_LexMsg {
	Str8      content;
	WATL_Tok* tok;
	WATL_Pos  pos;
};

typedef struct WATL_LexInfo WATL_LexInfo;
struct WATL_LexInfo {
	Slice_WATL_LexMsg msgs;
	Slice_WATL_Tok    toks;
	WATL_LexStatus    signal;
};

typedef struct Opts_watl_lex Opts_watl_lex;
struct Opts_watl_lex {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_toks;
	S32 max_msgs;
	B8  failon_unsupported_codepoints;
	B8  failon_pos_untrackable;
};

void watl_lex_api(WATL_LexInfo* info, Str8 source, Opts_watl_lex* opts);
#define watl_lex(source, ...) watl__lex(source, &(Opts_watl_lex){__VA_ARGS__})

#pragma endregion WATL

#pragma region Implementation

#pragma region File System

#include <apiset.h>
#include <apisetcconv.h>
#include <minwindef.h>
#include <minwinbase.h>
#include <handleapi.h>
#include <fileapi.h>
#if 0
HANDLE CreateFileA(
  [in]           LPCSTR                lpFileName,
  [in]           DWORD                 dwDesiredAccess,
  [in]           DWORD                 dwShareMode,
  [in, optional] LPSECURITY_ATTRIBUTES lpSecurityAttributes,
  [in]           DWORD                 dwCreationDisposition,
  [in]           DWORD                 dwFlagsAndAttributes,
  [in, optional] HANDLE                hTemplateFile
);
BOOL ReadFile(
  [in]                HANDLE       hFile,
  [out]               LPVOID       lpBuffer,
  [in]                DWORD        nNumberOfBytesToRead,
  [out, optional]     LPDWORD      lpNumberOfBytesRead,
  [in, out, optional] LPOVERLAPPED lpOverlapped
);
BOOL WriteFile(
  [in]                HANDLE       hFile,
  [in]                LPCVOID      lpBuffer,
  [in]                DWORD        nNumberOfBytesToWrite,
  [out, optional]     LPDWORD      lpNumberOfBytesWritten,
  [in, out, optional] LPOVERLAPPED lpOverlapped
);
#endif

inline
FileOpInfo file__read_contents(Str8 path, Opts__read_file_contents* opts) {
	slice_assert(path);
    assert(opts != nullptr);
	FileOpInfo result; file_read_contents_api(& result, path, * opts);
	return result;
}

void
file_read_contents_api(FileOpInfo* result, Str8* path, Opts__read_file_contents* opts)
{
	assert(result != nullptr);
	assert(opts   != nullptr);
	slice_assert(path);
	// Backing is required at this point
	slice_assert(opts->backing);

	// This will limit a path for V1 to be 16kb worth of codepoints.
	FMem_16KB   scratch   = {0};
	char const* path_cstr = str8_to_cstr_capped(path, fmem_slice(scratch) );

	HANDLE id_file = CreateFileA(
		path_cstr,
		GENERIC_READ,
		FILE_SHARE_READ,
		NULL,
		OPEN_EXISTING,
		FILE_ATTRIBUTE_NORMAL,
		NULL
	);
	B32 open_failed = id_file == INVALID_HANDLE_VALUE;
	if (open_failed) {
		DWORD  error_code = GetLastError();
		assert(error_code != 0);
		return;
	}

	LARGE_INTEGER file_size = {0};
	DWORD get_size_failed = ! GetFileSizeEx(id_file, & file_size);
	if   (get_size_failed) {
		assert(get_size_failed == INVALID_FILE_SIZE);
		return;
	}
	
	SliceByte buffer = mem_alloc(opts->backing, file_size);
	
	B32 not_enough_backing = buffer < file_size.QuadPart;
	if (not_enough_backing) {
		assert(not_enough_backing);
		result->content = (SliceByte){0};
		return;
	}

	if (opts->zero_backing) {
          slice_zero(pcast(SliceByte, opts->backing));
	}

	DWORD amount_read = 0;
	BOOL  read_result = ReadFile(
		id_file,
		buffer.ptr,
		file_size.QuadPart,
		& amount_read,
		nullptr
	);
	CloseHandle(id_file);
	
	B32 read_failed  = ! read_result;
	    read_failed |= amount_read != file_size.QuadPart;
	if (read_failed) {
		assert(read_failed);
		return;
	}

	result->content.ptr = buffer.ptr;
	result->content.len = file_size.QuadPart;
	return;	
}

#pragma endregion File System

#pragma endregion Implementation
