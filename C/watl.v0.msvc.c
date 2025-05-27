/*
WATL Exercise
Version: 0 (From Scratch, 1-Stage Compilation)

Vendor OS & Compiler: Windows 11, MSVC
*/

#pragma region Header

#pragma region DSL

#include <intrin.h>
#include <tmmintrin.h>
#include <wmmintrin.h>

typedef unsigned __int8  U8;
typedef signed   __int8  S8;
typedef unsigned __int16 U16;
typedef signed   __int16 S16;
typedef unsigned __int32 U32;
typedef signed   __int32 S32;
typedef unsigned __int64 U64;
typedef signed   __int64 S64;
typedef unsigned char    Byte;
typedef size_t           USIZE;
typedef ptrdiff_t        SSIZE;
typedef S8               B8;
typedef S16              B16;
typedef S32              B32;
enum {
	false,
	true,
	true_overflow,
};
#define glue_impl(A, B)                     A ## B
#define glue(A, B)                          glue_impl(A, B)
#define stringify_impl(S)                   #S
#define stringify(S)                        stringify_impl(S)
#define tmpl(prefix, type)                  prefix ## _ ## type

#define farray_len(array)                   (SSIZE)sizeof(array) / size_of((array)[0])
#define farray_init(type, ...)              (type[]){__VA_ARGS__}
#define def_struct(symbol)                  struct symbol symbol;   struct symbol
#define def_enum(underlying_type, symbol)   underlying_type symbol; enum   symbol
#define fn(symbol)                          symbol
#define fn_type(symbol, return_type, ...)   return_type (symbol) (__VA_ARGS__)
#define optional_args(symbol, ...)          &(symbol){__VA_ARGS__}
#define ret_type(type)                      type
#define local_persist                       static
#define typeof                              __typeof__

#define cast(type, data)                    ((type)(data))
#define pcast(type, data)                   * cast(type*, & (data))
#define nullptr                             cast(void*, 0)
#define size_of(data)                       cast(SSIZE, sizeof(data))
#define kilo(n)                             (cast(USIZE, n) << 10)
#define mega(n)                             (cast(USIZE, n) << 20)
#define giga(n)                             (cast(USIZE, n) << 30)
#define tera(n)                             (cast(USIZE, n) << 40)

#define range_iter(type, cursor, m_begin, op, m_end) \
	tmpl(Iter_Range,type) cursor = {                 \
		.r = {(m_begin), (m_end)},                   \
		.cursor = (m_begin) };                       \
	iter.cursor op iter.r.end;                       \
	++ iter.cursor
#define def_range(type)                                                         \
	        def_struct(tmpl(     Range,type)) { type begin; type end; };        \
	typedef def_struct(tmpl(Iter_Range,type)) { tmpl(Range,type) r; type idx; }

typedef def_range(U32);
typedef def_range(SSIZE);

#pragma endregion DSL

#pragma region Memory

#define align_pow2(x, b)         (((x) + (b) - 1) & ( ~((b) - 1)))
#define align_struct(type_width) ((SSIZE)(((type_width) + 7) / 8 * 8))

void* memory_copy            (void* restrict dest, void const* restrict src, USIZE length);
void* memory_copy_overlapping(void* restrict dest, void const* restrict src, USIZE length);
B32   memory_zero            (void* dest, USIZE length);

#define def_Slice(type)        \
def_struct(tmpl(Slice,type)) { \
	type* ptr;                 \
	SSIZE len;                 \
}

typedef def_Slice(void);
typedef def_Slice(Byte);

#define slice_fmem(mem) (Slice_Byte){ mem, size_of(mem) }

#define slice_assert(slice) do {    \
	assert((slice).ptr != nullptr); \
	assert((slice).len > 0);        \
} while(0)

#define slice_byte(slice)         (Slice_Byte){(slice).ptr, (slice).len * size_of_slice_type(slice)}
#define size_of_slice_type(slice) size_of( * (slice).ptr )

void slice__copy(Slice_Byte dest, SSIZE dest_typewidth, Slice_Byte src, SSIZE src_typewidth);
#define slice_copy(dest, src) slice__copy( slice_byte(dest), size_of_slice_type(dest), slice_byte(src), size_of_slice_type(src))

#define slice_iter(container, iter) typeof((container).ptr) iter = (container).ptr; iter != ((container).ptr + (container).len); ++ iter

#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) {  \
	.ptr = farray_init(type, __VA_ARGS__),                      \
	.len = farray_len( farray_init(type, __VA_ARGS__))          \
}

#pragma endregion Memory

#pragma region Strings

typedef unsigned char UTF8;
typedef def_Slice(UTF8);
typedef Slice_UTF8 Str8;
typedef def_Slice(Str8);

#define lit(string_literal) (Str8){ string_literal, size_of(string_literal) - 1 }

#pragma endregion Strings

#pragma region Allocator Interface

typedef def_enum(U32, AllocatorOp) {
	AllocatorOp_Alloc = 0,
	AllocatorOp_Alloc_NoZero, // If Alloc exist, so must No_Zero
	AllocatorOp_Free,
	AllocatorOp_Reset,
	AllocatorOp_Grow,
	AllocatorOp_Grow_NoZero,
	AllocatorOp_Shrink,
	AllocatorOp_Shrink_NoZero,
	AllocatorOp_Rewind,
	AllocatorOp_SavePoint,
	AllocatorOp_Query, // Must always be implemented
};

/*
These are good to enforce constraints via asserts,
however for situations that have hard constraints, 
it may be better to enforce strict allocator type/s for the receiving data structure or code path.
*/
typedef def_enum(U64, AllocatorQueryFlags) {
	AllocatorQuery_Alloc        = (1 << 0),
	AllocatorQuery_Free         = (1 << 1),
	// Wipe the allocator's state
	AllocatorQuery_Reset        = (1 << 2), 
	// Supports both grow and shrink
	AllocatorQuery_Shrink       = (1 << 4),
	AllocatorQuery_Grow         = (1 << 5),	
	AllocatorQuery_Resize       = AllocatorQuery_Grow | AllocatorQuery_Shrink, 
	// Ability to rewind to a save point (ex: arenas, stack), must also be able to save such a point
	AllocatorQuery_Rewind       = (1 << 6), 
};

typedef def_struct(AllocatorProc_In) {
	void*        data;
	AllocatorOp  op;
	SSIZE        requested_size;
	SSIZE        alignment;
	Slice_Byte   old_allocation;
};
typedef def_struct(AllocatorProc_Out) {
	Slice_Byte          allocation;
	AllocatorQueryFlags features;
	SSIZE               left;
	SSIZE               max_alloc;
	SSIZE               min_alloc;
	B32                 continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
};
typedef void fn(AllocatorProc) (AllocatorProc_In In, AllocatorProc_Out* Out);

typedef def_struct(AllocatorInfo) {
	AllocatorProc* proc;
	void*          data;
};

// This the point right after the last allocation usually.
typedef def_struct(AllocatorSP) {
	USIZE slot;
};

#define MEMORY_ALIGNMENT_DEFAULT (2 * size_of(void*)))

AllocatorQueryFlags allocator_query(AllocatorInfo ainfo);

void        mem_free      (AllocatorInfo ainfo, Slice_Byte mem);
void        mem_reset     (AllocatorInfo ainfo);
void        mem_rewind    (AllocatorInfo ainfo, AllocatorSP save_point);
AllocatorSP mem_save_point(AllocatorInfo ainfo);

typedef def_struct(Opts_mem_alloc)  { SSIZE alignment; B32 no_zero; };
typedef def_struct(Opts_mem_grow)   { SSIZE alignment; B32 no_zero; };
typedef def_struct(Opts_mem_shrink) { SSIZE alignment; };
typedef def_struct(Opts_mem_resize) { SSIZE alignment; B32 no_zero; };

Slice_Byte mem__alloc (AllocatorInfo ainfo,                 SSIZE size, Opts_mem_alloc*  opts);
Slice_Byte mem__grow  (AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_grow*   opts);
Slice_Byte mem__resize(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_resize* opts);
Slice_Byte mem__shrink(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_shrink* opts);

#define mem_alloc(ainfo, size, ...)       mem__alloc (ainfo,      size, optional_args(Opts_mem_alloc,  __VA_ARGS__))
#define mem_grow(ainfo, size, ...)        mem__grow  (ainfo,      size, optional_args(Opts_mem_grow,   __VA_ARGS__))
#define mem_resize(ainfo, mem, size, ...) mem__resize(ainfo, mem, size, optional_args(Opts_mem_resize, __VA_ARGS__))
#define mem_shrink(ainfo, mem, size, ...) mem__shrink(ainfo, mem, size, optional_args(Opts_mem_shrink, __VA_ARGS__))

#define alloc_type(ainfo, type, ...)       (type*)             mem__alloc(ainfo, size_of(type),        optional_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ mem__alloc(ainfo, size_of(type) * num,  optional_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }

#pragma endregion Allocator Interface

#pragma region Hashing
void hash64_djb8(U64* hash, Slice_Byte bytes);
#pragma endregion Hashing

#pragma region Key Table 1-Layer Linear (KT1L)

#define def_KT1L_Slot(type)        \
def_struct(tmpl(KT1L_Slot,type)) { \
	type value;                    \
	U64  key;                      \
}

#define def_KT1L(type)                       \
	        def_Slice(tmpl(KT1L_Slot,type)); \
	typedef tmpl(Slice_KT1L_Slot,type) tmpl(KT1L,type)

typedef Slice_Byte KT1L_Byte;
typedef def_struct(KT1L_Info) {
	AllocatorInfo backing;
	SSIZE slot_size;
	SSIZE key_offset;
	SSIZE type_width;
};
void kt1l__populate(KT1L_Byte* kt, KT1L_Info info, Slice_Byte values, SSIZE num_values );
#define kt1l_populate(kt, info, values, num_values, hash_op) 

#pragma endregion KT1L

#pragma region Key Table 1-Layer Chained-Chunked-Cells (KT1CX)

#define def_KT1CX_Slot(type)      \
def_struct(tmpl(KT_Slot,type)) {  \
	type value;                   \
	U64  key;                     \
	B32  occupied;                \
}

#define def_KT1CX_Cell(type, depth)   \
def_struct(tmpl(KT_Cell,type)) {      \
	tmpl(KT_Slot,type)  slots[depth]; \
	tmpl(KT_Cell,type)* next;         \
}

#define def_KT1CX(type)                 \
def_struct(tmpl(KT,type)) {             \
	tmpl(Slice_KT_Cell,type) cell_pool; \
	tmpl(Slice_KT_Cell,type) table;     \
} 

#define def_KT1CX_Interface(symbol)

typedef def_struct(KT_Byte_Slot) {
	U64   key;
	B32   occupied;
};
typedef def_struct(KT_Byte) {
	Slice_Byte cell_pool;
	Slice_Byte table;
};
typedef def_struct(KT_ByteMeta) {
	SSIZE         table_size;
	SSIZE         cell_depth;
	SSIZE         type_width;
	Str8          type_name;
};
typedef def_struct(KT_Info) {
	AllocatorInfo backing_table;
	AllocatorInfo backing_cells;
	SSIZE         table_size;
	SSIZE         cell_depth;
	SSIZE         type_width;
	Str8          type_name;
};
void kt1cx__init   (KT_Info info, KT_Byte* result);
void kt1cx__clear  (KT_Byte* kt,  KT_ByteMeta meta);
void kt1cx__slot_id(KT_Byte* kt,  KT_ByteMeta meta);
void kt1cx__get    (KT_Byte* kt,  KT_ByteMeta meta);
void kt1cx__set    (KT_Byte* kt,  KT_ByteMeta meta);

#define kt1cx_init()
#define kt1cx_clear()
#define kt1cx_slot_id()
#define kt1cx_get()
#define kt1cx_set()

#pragma endregion KT1CX

#pragma region String Operations

inline B32 char_is_upper(U8 c) { return('A' <= c && c <= 'Z'); }
inline U8  char_to_lower(U8 c) { if (char_is_upper(c)) { c += ('a' - 'A'); } return(c); }

Str8 str8_from_u32(AllocatorInfo ainfo, U32 num, U32 radix, U8 min_digits, U8 digit_group_separator);

typedef def_KT1L_Slot(Str8);
typedef def_KT1L(Str8);

Str8 str8__fmt(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_Str8* tokens);
#define str8_fmt(tbl_backing, buf_backing, fmt_template, ...) str8__fmt(tbl_backing, buf_backing, fmt_template, slice_arg_from_array(__VA_ARGS__))

typedef def_KT1CX_Slot(Str8);
typedef def_KT1CX_Cell(Str8, 4);
typedef def_Slice(KT_Cell_Str8);
typedef def_KT1CX(Str8);
typedef def_struct(Str8Cache) {
	AllocatorInfo str_reserve;
	AllocatorInfo cell_reserve;
	AllocatorInfo tbl_backing;
	KT_Str8       kt;
};

void      str8cache_init(Str8Cache* cache, AllocatorInfo str_reserve, AllocatorInfo cell_reserve, AllocatorInfo tbl_backing);
Str8Cache str8cache_make(                  AllocatorInfo str_reserve, AllocatorInfo cell_reserve, AllocatorInfo tbl_backing);

void str8cache_clear(KT_Str8 kt);
void str8cache_get  (KT_Str8 kt,  U64 key);
void str8cache_set  (KT_Str8* kt, U64 key, Str8 value);

Str8 cache_str8(Str8Cache* cache, Str8 str);

typedef def_struct(Str8Gen) {
	AllocatorInfo backing;
	UTF8*         ptr;
	SSIZE         len;
};
void    str8gen_init(Str8Gen* gen, AllocatorInfo backing);
Str8Gen str8gen_make(              AllocatorInfo backing);

void str8gen_append_str8(Str8Gen* gen, Str8 str);
void str8gen__append_fmt(Str8Gen* gen, Str8 fmt_template, Slice_Str8* tokens);

#define str8gen_append_fmt(gen, fmt_template, ...) str8gen__append_fmt(gen, fmt_template, slice_from_array(Str8, __VA_ARGS__))

#pragma endregion String Operations

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

void assert_handler(Str8 condition, Str8 path_file, Str8 function, S64 line, Str8 message, ...);

#pragma endregion Debug

#pragma region File System

typedef def_struct(FileOpInfo) {
	Slice_Byte content;
};
typedef def_struct(Opts_read_file_contents) {
	AllocatorInfo backing;
	B32           zero_backing;
};
void api_file_read_contents(FileOpInfo* result, Str8 path, Opts_read_file_contents opts);
void file_write_str8       (Str8 path, Str8 content);

FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents* opts);
#define file_read_contents(path, ...) file__read_contents(path, &(Opts_read_file_contents){__VA_ARGS__})

#pragma endregion File System

#pragma region WATL

typedef def_struct(WATL_Tok) {
	UTF8* code;
};
typedef def_Slice(WATL_Tok);

typedef def_enum(U32, WATL_LexStatus) {
	WATL_LexStatus_MemFail_Alloc,
	WATL_LexStatus_MemFail_SliceConstraintFail,
	WATL_LexStatus_PosUntrackable,
	WATL_LexStatus_UnsupportedCodepoints,
	WATL_LexStatus_MessageOverflow,
};
typedef def_struct(WATL_Pos) {
	S32 line;
	S32 column;
};
typedef def_struct(WATL_LexMsg) {
	Str8      content;
	WATL_Tok* tok;
	WATL_Pos  pos;
};
typedef def_Slice(WATL_LexMsg);

typedef def_struct(WATL_LexInfo) {
	Slice_WATL_LexMsg msgs;
	Slice_WATL_Tok    toks;
	WATL_LexStatus    signal;
};
typedef def_struct(Opts_watl_lex) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_toks;
	S32 max_msgs;
	B8  failon_unsupported_codepoints;
	B8  failon_pos_untrackable;
};
void         api_watl_lex(WATL_LexInfo* info, Str8 source, Opts_watl_lex* opts);
WATL_LexInfo watl__lex   (                    Str8 source, Opts_watl_lex* opts);
#define watl_lex(source, ...) watl__lex(source, &(Opts_watl_lex){__VA_ARGS__})

typedef Str8 WATL_Node;
typedef def_Slice(WATL_Node);
typedef Slice_WATL_Node WATL_Line;
typedef def_Slice(WATL_Line);

typedef def_struct(WATL_ParseMsg) {
	Str8 content;
	WATL_Line line;
	WATL_Tok* tok;
	WATL_Pos  pos;
};
typedef def_Slice(WATL_ParseMsg);

typedef def_enum(WATL_ParseStatus) {
	WATL_ParseStatus_MemFail_Alloc,
	WATL_ParseStatus_MemFail_SliceConstraintFail,
	WATL_ParseStatus_PosUntrackable,
	WATL_ParseStatus_UnsupportedTokens,
	WATL_ParseStatus_MessageOverflow,
};

typedef def_struct(WATL_ParseInfo) {
	Slice_WATL_Line lines;
	Slice_WATL_ParseMsg msgs;
	WATL_ParseStatus    signal;
};
typedef def_struct(Opts_watl_parse) {
	AllocatorInfo backing_nodes;
	AllocatorInfo backing_lines;
	Str8Cache*    str_cache;
};
void           api_watl_parse(WATL_ParseInfo* info, Slice_WATL_Tok tokens, Opts_watl_parse* opts);
WATL_ParseInfo watl__parse   (                      Slice_WATL_Tok tokens, Opts_watl_parse* opts);
#define watl_parse(tokens, ...) watl__parse(tokens, &(Opts_watl_parse){__VA_ARGS__})

#pragma endregion WATL

#pragma endregion Header

#pragma region Implementation

#pragma region Memory Operations

inline
void* memory_copy(void* restrict dest, void const* restrict src, USIZE length)
{
	if (dest == nullptr || src == nullptr || length == 0) {
		return nullptr;
	}
	// https://learn.microsoft.com/en-us/cpp/intrinsics/movsb?view=msvc-170
	memcpy(dest, src, length);
	return dest;
}

inline
void* memory_copy_overlapping(void* restrict dest, void const* restrict src, USIZE length)
{
	if (dest == nullptr || src == nullptr || length == 0) {
		return nullptr;
	}
	// https://learn.microsoft.com/en-us/cpp/intrinsics/movsb?view=msvc-170
	memmove(dest, src, length);
	return dest;
}

inline 
B32 memory_zero(void* dest, USIZE length)
{
	if (dest == nullptr || length <= 0) {
		return false;
	}
	memset((unsigned char*)dest, 0, length);
	return true;
}

inline
void slice__copy(Slice_Byte dest, SSIZE dest_typewidth, Slice_Byte src, SSIZE src_typewidth) {
	assert(dest.len >= src.len);
	slice_assert(dest);
	slice_assert(src);
	memory_copy(dest.ptr, src.ptr, src.len);
}

#pragma endregion Memory Operations

#pragma region Allocator Interface

inline
AllocatorQueryFlags allocator_query(AllocatorInfo ainfo) { 
	assert(info.proc != nullptr);
	AllocatorProc_Out out; ainfo.proc((AllocatorProc_In){ .data = ainfo.data, .op = AllocatorOp_Query}, & out); return out.features;
}

inline
void mem_free(AllocatorInfo ainfo, Slice_Byte mem) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Free, .old_allocation = mem}, &(AllocatorProc_Out){});
}

inline
void mem_reset(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Reset}, &(AllocatorProc_Out){});
}

inline
Slice_Byte mem__alloc(AllocatorInfo ainfo, SSIZE size, Opts_mem_alloc* opts) {
	assert(info.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In  in = {
		.data           = ainfo.data,
		.op             = opts->no_zero ?  AllocatorOp_Alloc_NoZero : AllocatorOp_Alloc,
		.requested_size = size,
		.alignment      = opts->alignment,
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out); 
	return out.allocation;
}

inline
Slice_Byte mem__grow(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_grow* opts) {
	assert(info.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In in = {
		.data           = ainfo.data,
		.op             = opts->no_zero ? AllocatorOp_Grow_NoZero : AllocatorOp_Grow,
		.requested_size = size,
		.alignment      = opts->alignment,
		.old_allocation = mem
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out);
	return out.allocation;
}



#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)



#pragma endregion FArena

#pragma region Key Table 1-Layer Linear (KT1L)

inline
void kt1l__populate(KT1L_Byte* kt, KT1L_Info info, Slice_Byte values, SSIZE num_values )
{
	assert(kt != nullptr);
	* kt = alloc_slice(info.backing, Byte, info.slot_size * num_values );
	slice_assert(* kt);
	for (range_iter(U32, iter, 0, <, num_values)) {
        SSIZE      slot_offset  = iter.idx * info.slot_size;
        Slice_Byte slot_value   = { &kt->ptr[slot_offset], info.type_width };
        U64*       slot_key     = (U64*)&kt->ptr[slot_offset + info.key_offset];
        SSIZE      value_offset = iter.idx * info.type_width;
        Slice_Byte value        = { &values.ptr[value_offset], info.type_width };
        slice_copy(slot_value, value);
        hash64_djb8(slot_key, slot_value);
    }
}

#pragma endregion KT1l

#pragma region File System

#define NOMINMAX
#define WIN32_LEAN_AND_MEAN
#define WIN32_MEAN_AND_LEAN
#define VC_EXTRALEAN
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
#undef NOMINMAX
#undef WIN32_LEAN_AND_MEAN
#undef WIN32_MEAN_AND_LEAN
#undef VC_EXTRALEAN

inline
FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents* opts) {
	slice_assert(path);
    assert(opts != nullptr);
	FileOpInfo result; file_read_contents_api(& result, path, * opts);
	return result;
}

void
file_read_contents_api(FileOpInfo* result, Str8 path, Opts_read_file_contents opts)
{
	assert(result != nullptr);
	slice_assert(path);
	// Backing is required at this point
	slice_assert(opts->backing);

	// This will limit a path for V1 to be 32kb worth of codepoints.
	local_persist U8 scratch[KILO(32)];
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
	
	Slice_Byte buffer = mem_alloc(opts->backing, file_size.QuadPart);
	
	B32 not_enough_backing = buffer.len < file_size.QuadPart;
	if (not_enough_backing) {
		assert(not_enough_backing);
		result->content = (Slice_Byte){0};
		return;
	}

	if (opts->zero_backing) {
		slice_zero(buffer);
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

#pragma region Debug

void assert_handler(Str8 condition, Str8 path_file, Str8 function, Str8 line, Str8 message, ...) {

}

#pragma endregion Debug

#pragma endregion Implementation

int main()
{

}
