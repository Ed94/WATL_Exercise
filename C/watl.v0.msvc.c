/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, MSVC & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: MSVC 19.43, C-Stanard: 23
*/

#pragma warning(disable: 4100)
#pragma warning(disable: 4127)
#pragma warning(disable: 4201)
#pragma warning(disable: 4702)
#pragma warning(disable: 4710)
#pragma warning(disable: 5045)

#pragma region Header

#pragma region DSL
typedef unsigned __int8  U8;
typedef signed   __int8  S8;
typedef unsigned __int16 U16;
typedef signed   __int16 S16;
typedef unsigned __int32 U32;
typedef signed   __int32 S32;
typedef unsigned __int64 U64;
typedef signed   __int64 S64;
typedef unsigned char    Byte;
typedef unsigned __int64 USIZE;
typedef          __int64 SSIZE;
typedef S8               B8;
typedef S16              B16;
typedef S32              B32;
enum {
	false = 0,
	true  = 1,
	true_overflow,
};
#define glue_impl(A, B)                     A ## B
#define glue(A, B)                          glue_impl(A, B)
#define stringify_impl(S)                   #S
#define stringify(S)                        stringify_impl(S)
#define tmpl(prefix, type)                  prefix ## _ ## type

#define byte_pad(amount, ...)               Byte glue(_PAD_, __VA_ARGS__) [amount]
#define farray_len(array)                   (SSIZE)sizeof(array) / size_of( typeof((array)[0]))
#define farray_init(type, ...)              (type[]){__VA_ARGS__}
#define def_farray(type, len)               type A ## len ## _ ## type[len]
#define def_enum(underlying_type, symbol)   underlying_type symbol; enum   symbol
#define def_struct(symbol)                  struct symbol symbol;   struct symbol
#define def_union(symbol)                   union  symbol symbol;   union  symbol
#define fn(symbol)                          symbol
#define opt_args(symbol, ...)               &(symbol){__VA_ARGS__}
#define ret_type(type)                      type
#define local_persist                       static
#define global                              static
#define offset_of(type, member)             cast(SSIZE, & (((type*) 0)->member))
#define static_assert                       _Static_assert
#define typeof                              __typeof__
#define typeof_ptr(ptr)                     typeof(ptr[0])                 
#define typeof_same(a, b)                   _Generic((a), typeof((b)): 1, default: 0)

#define cast(type, data)                    ((type)(data))
#define pcast(type, data)                   * cast(type*, & (data))
#define nullptr                             cast(void*, 0)
#define size_of(data)                       cast(SSIZE, sizeof(data))
#define kilo(n)                             (cast(SSIZE, n) << 10)
#define mega(n)                             (cast(SSIZE, n) << 20)
#define giga(n)                             (cast(SSIZE, n) << 30)
#define tera(n)                             (cast(SSIZE, n) << 40)

#define range_iter(type, iter, m_begin, op, m_end)  \
	tmpl(Iter_Range,type) iter = {                  \
		.r = {(m_begin), (m_end)},                  \
		.cursor = (m_begin) };                      \
	iter.cursor op iter.r.end;                      \
	++ iter.cursor

#define def_range(type)                                                         \
	        def_struct(tmpl(     Range,type)) { type begin; type end; };        \
	typedef def_struct(tmpl(Iter_Range,type)) { tmpl(Range,type) r; type cursor; }

typedef def_range(S32);
typedef def_range(U32);
typedef def_range(SSIZE);

typedef void fn(VoidFn) (void);
#pragma endregion DSL

#pragma region Debug
#if !defined(BUILD_DEBUG)
#define debug_trap()
#define assert(cond)
#define assert_msg(cond, msg, ...)
#define assert_trap(cond)
#endif
#if defined(BUILD_DEBUG)
#define debug_trap()      __debugbreak()
#define assert_trap(cond) do { if (cond) __debug_trap(); } while(0)
#define assert(cond)      assert_msg(cond, nullptr)
#define assert_msg(cond, msg, ...) do {       \
	if (! (cond))                             \
	{                                         \
		assert_handler(                       \
			stringify(cond),                  \
			__FILE__,                         \
			__func__,                         \
			cast(S64, __LINE__),              \
			msg,                              \
			## __VA_ARGS__);                  \
		debug_trap();                         \
	}                                         \
} while(0)
void assert_handler( char const* condition, char const* file, char const* function, S32 line, char const* msg, ... );
#endif
#pragma endregion Debug

#pragma region Memory
inline SSIZE align_pow2(SSIZE x, SSIZE b);

#define align_struct(type_width) ((SSIZE)(((type_width) + 7) / 8 * 8))

#define assert_bounds(point, start, end) do { \
	SSIZE pos_point = cast(SSIZE, point);     \
	SSIZE pos_start = cast(SSIZE, start);     \
	SSIZE pos_end   = cast(SSIZE, end);       \
	assert(pos_start <= pos_point);           \
	assert(pos_point <= pos_end);             \
} while(0)

void* memory_copy            (void* restrict dest, void const* restrict src, USIZE length);
void* memory_copy_overlapping(void* restrict dest, void const* restrict src, USIZE length);
B32   memory_zero            (void* dest, USIZE length);

#define def_Slice(type)        \
def_struct(tmpl(Slice,type)) { \
	type* ptr;                 \
	SSIZE len;                 \
}
#define slice_assert(slice) do { assert((slice).ptr != nullptr); assert((slice).len > 0); } while(0)
#define slice_end(slice)          ((slice).ptr + (slice).len)
#define size_of_slice_type(slice) size_of( * (slice).ptr )

typedef def_Slice(void);
typedef def_Slice(Byte);
#define slice_byte(slice) ((Slice_Byte){cast(Byte*, (slice).ptr), (slice).len * size_of_slice_type(slice)})
#define slice_fmem(mem)   ((Slice_Byte){ mem, size_of(mem) })

void slice__copy(Slice_Byte dest, SSIZE dest_typewidth, Slice_Byte src, SSIZE src_typewidth);
void slice__zero(Slice_Byte mem, SSIZE typewidth);
#define slice_copy(dest, src) do {             \
	static_assert(typeof_same(dest, src)); \
	slice__copy(slice_byte(dest),  size_of_slice_type(dest), slice_byte(src), size_of_slice_type(src)); \
} while (0)
#define slice_zero(slice) slice__zero(slice_byte(slice), size_of_slice_type(slice))

#define slice_iter(container, iter)                 \
	typeof((container).ptr) iter = (container).ptr; \
	iter != slice_end(container);                   \
	++ iter
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) {  \
	.ptr = farray_init(type, __VA_ARGS__),                      \
	.len = farray_len( farray_init(type, __VA_ARGS__))          \
}

#define check_nil(nil, p) ((p) == 0 || (p) == nil)
#define set_nil(nil, p)   ((p) = nil)

#define sll_stack_push_n(f, n, next) do { (n)->next = (f); (f) = (n); } while(0)

#define sll_queue_push_nz(nil, f, l, n, next) \
(                                             \
	check_nil(nil, f) ? (                     \
		(f) = (l) = (n),                      \
		set_nil(nil, (n)->next)               \
	)                                         \
	: (                                       \
		(l)->next=(n),                        \
		(l) = (n),                            \
		set_nil(nil,(n)->next)                \
	)                                         \
)
#define sll_queue_push_n(f, l, n, next) sll_queue_push_nz(0, f, l, n, next)
#pragma endregion Memory

#pragma region Math
#define min(A, B)       (((A) < (B)) ? (A) : (B))
#define max(A, B)       (((A) > (B)) ? (A) : (B))
#define clamp_bot(X, B) max(X, B)
#pragma endregion Math

#pragma region Strings
typedef unsigned char UTF8;
typedef def_Slice(UTF8);
typedef Slice_UTF8 Str8;
typedef def_Slice(Str8);
#define lit(string_literal) (Str8){ (UTF8*) string_literal, size_of(string_literal) - 1 }
#pragma endregion Strings

#pragma region Allocator Interface
typedef def_enum(U32, AllocatorOp) {
	AllocatorOp_Alloc_NoZero = 0, // If Alloc exist, so must No_Zero
	AllocatorOp_Alloc,
	AllocatorOp_Free,
	AllocatorOp_Reset,
	AllocatorOp_Grow_NoZero,
	AllocatorOp_Grow,
	AllocatorOp_Shrink,
	AllocatorOp_Rewind,
	AllocatorOp_SavePoint,
	AllocatorOp_Query, // Must always be implemented
};
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
	SSIZE        requested_size;
	SSIZE        alignment;
	Slice_Byte   old_allocation;
	AllocatorOp  op;
	byte_pad(4);
};
typedef struct AllocatorProc_Out AllocatorProc_Out;
typedef void fn(AllocatorProc) (AllocatorProc_In In, AllocatorProc_Out* Out);
typedef def_struct(AllocatorSP) {
	AllocatorProc* type_sig;
	SSIZE          slot;
};
struct AllocatorProc_Out {
	union {
		Slice_Byte  allocation;
		AllocatorSP save_point;
	};
	AllocatorQueryFlags features;
	SSIZE               left; // Contiguous memory left
	SSIZE               max_alloc;
	SSIZE               min_alloc;
	B32                 continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
	byte_pad(4);
};
typedef def_struct(AllocatorInfo) {
	AllocatorProc* proc;
	void*          data;
};
static_assert(size_of(AllocatorSP) <= size_of(Slice_Byte));

#define MEMORY_ALIGNMENT_DEFAULT (2 * size_of(void*))

AllocatorQueryFlags allocator_query(AllocatorInfo ainfo);

void        mem_free      (AllocatorInfo ainfo, Slice_Byte mem);
void        mem_reset     (AllocatorInfo ainfo);
void        mem_rewind    (AllocatorInfo ainfo, AllocatorSP save_point);
AllocatorSP mem_save_point(AllocatorInfo ainfo);

typedef def_struct(Opts_mem_alloc)  { SSIZE alignment; B32 no_zero; byte_pad(4); };
typedef def_struct(Opts_mem_grow)   { SSIZE alignment; B32 no_zero; byte_pad(4); };
typedef def_struct(Opts_mem_shrink) { SSIZE alignment; };
typedef def_struct(Opts_mem_resize) { SSIZE alignment; B32 no_zero; byte_pad(4); };

Slice_Byte mem__alloc (AllocatorInfo ainfo,                 SSIZE size, Opts_mem_alloc*  opts);
Slice_Byte mem__grow  (AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_grow*   opts);
Slice_Byte mem__resize(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_resize* opts);
Slice_Byte mem__shrink(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_shrink* opts);

#define mem_alloc(ainfo, size, ...)       mem__alloc (ainfo,      size, opt_args(Opts_mem_alloc,  __VA_ARGS__))
#define mem_grow(ainfo,   mem, size, ...) mem__grow  (ainfo, mem, size, opt_args(Opts_mem_grow,   __VA_ARGS__))
#define mem_resize(ainfo, mem, size, ...) mem__resize(ainfo, mem, size, opt_args(Opts_mem_resize, __VA_ARGS__))
#define mem_shrink(ainfo, mem, size, ...) mem__shrink(ainfo, mem, size, opt_args(Opts_mem_shrink, __VA_ARGS__))

#define alloc_type(ainfo, type, ...)       (type*)             mem__alloc(ainfo, size_of(type),        opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ mem__alloc(ainfo, size_of(type) * num,  opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }
#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)
typedef def_struct(Opts_farena) {
	Str8  type_name;
	SSIZE alignment;
};
typedef def_struct(FArena) {
	void* start;
	SSIZE capacity;
	SSIZE used;
};
FArena      farena_make  (Slice_Byte byte);
void        farena_init  (FArena* arena, Slice_Byte byte);
Slice_Byte  farena__push (FArena* arena, SSIZE amount, SSIZE type_width, Opts_farena* opts);
void        farena_reset (FArena* arena);
void        farena_rewind(FArena* arena, AllocatorSP save_point);
AllocatorSP farena_save  (FArena  arena);

void farena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out);
#define ainfo_farena(arena) (AllocatorInfo){ .proc = farena_allocator_proc, .data = & arena }

#define farena_push(arena, type, ...) \
cast(type*, farena__push(arena, size_of(type), 1, opt_args(Opts_farena_push, lit(stringify(type)), __VA_ARGS__))).ptr

#define farena_push_array(arena, type, amount, ...) \
(Slice ## type){ farena__push(arena, size_of(type), amount, opt_args(Opts_farena_push, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion FArena

#pragma region OS
typedef def_struct(OS_SystemInfo) {
	SSIZE target_page_size;
};
typedef def_struct(Opts_vmem) {
	SSIZE base_addr;
	B32   no_large_pages;
	byte_pad(4);
};
void os_init(void);
OS_SystemInfo* os_system_info(void);

inline B32   os__vmem_commit(void* vm, SSIZE size, Opts_vmem* opts);
inline Byte* os__vmem_reserve(SSIZE size, Opts_vmem* opts);
inline void  os_vmem_release(void* vm, SSIZE size);

#define os_vmem_reserve(size, ...)    os__vmem_reserve(size, opt_args(Opts_vmem, __VA_ARGS__))
#define os_vmem_commit(vm, size, ...) os__vmem_commit(vm, size, opt_args(Opts_vmem, __VA_ARGS__))
#pragma endregion OS

#pragma region VArena (Virutal Address Space Arena)
typedef Opts_farena Opts_varena;
typedef def_enum(U32, VArenaFlags) { 
	VArenaFlag_NoLargePages = (1 << 0),
};
typedef def_struct(VArena) {
	SSIZE reserve_start;
	SSIZE reserve;
	SSIZE commit_size;
	SSIZE committed;
	SSIZE commit_used;
	VArenaFlags flags;
	byte_pad(4);
};
typedef def_struct(Opts_varena_make) {
	SSIZE       base_addr;
	SSIZE       reserve_size;
	SSIZE       commit_size;
	VArenaFlags flags;
	byte_pad(4);
};
VArena* varena__make(Opts_varena_make* opts);
#define varena_make(...) varena__make(opt_args(Opts_varena_make, __VA_ARGS__))

Slice_Byte  varena__push  (VArena* arena, SSIZE amount, SSIZE type_width, Opts_varena* opts);
void        varena_release(VArena* arena);
void        varena_rewind (VArena* arena, AllocatorSP save_point);
void        varena_reset  (VArena* arena);
AllocatorSP varena_save   (VArena* arena);

void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out); 
#define ainfo_varena(varena) (AllocatorInfo) { .proc = varena_allocator_proc, .data = varena }

#define varena_push(arena, type, ...) \
cast(type*, varena__push(arena, 1, size_of(type), opt_args(Opts_varena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define varena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ varena__push(arena, size_of(type), amount, opt_args(Opts_varena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion VArnea

#pragma region Arena (Casey-Ryan Composite Arenas)
typedef Opts_varena Opts_arena;
typedef def_enum(U32, ArenaFlags) {
	ArenaFlag_NoLargePages = (1 << 0),
	ArenaFlag_NoChain      = (1 << 1),
};
typedef def_struct(Arena) {
	VArena*    backing;
	Arena*     prev;
	Arena*     current;
	SSIZE      base_pos;
	SSIZE      pos;
	ArenaFlags flags;
	byte_pad(4);
};
typedef Opts_varena_make Opts_arena_make;
Arena*      arena__make  (Opts_arena_make* opts);
Slice_Byte  arena__push  (Arena* arena, SSIZE amount, SSIZE type_width, Opts_arena* opts);
void        arena_release(Arena* arena);
void        arena_reset  (Arena* arena);
void        arena_rewind (Arena* arena, AllocatorSP save_point);
AllocatorSP arena_save   (Arena* arena);

void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out);
#define ainfo_arena(arena) (AllocatorInfo){ .proc = arena_allocator_proc, .data = arena }

#define arena_make(...) arena__make(opt_args(Opts_arena_make, __VA_ARGS__))

#define arena_push(arena, type, ...) \
cast(type*, arena__push(arena, 1, size_of(type), opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define arena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ arena__push(arena, size_of(type), amount, opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion Arena

#pragma region Hashing
inline
void hash64_djb8(U64* hash, Slice_Byte bytes) {
	for (U8 const* elem = bytes.ptr; elem != (bytes.ptr + bytes.len); ++ elem) {
		*hash = (((*hash) << 8) + (*hash)) + (*elem);
	}
}
#pragma endregion Hashing

#pragma region Key Table 1-Layer Linear (KT1L)
#define def_KT1L_Slot(type)        \
def_struct(tmpl(KT1L_Slot,type)) { \
	U64  key;                      \
	type value;                    \
}
#define def_KT1L(type)                       \
	        def_Slice(tmpl(KT1L_Slot,type)); \
	typedef tmpl(Slice_KT1L_Slot,type) tmpl(KT1L,type)

typedef Slice_Byte KT1L_Byte;
typedef def_struct(KT1L_Info) {
	AllocatorInfo backing;
	SSIZE slot_size;
	SSIZE kt_value_offset;
	SSIZE type_width;
	Str8  type_name;
};
SSIZE kt1l__populate_slice_a2(KT1L_Byte* kt, KT1L_Info info, Slice_Byte values, SSIZE num_values );
#define kt1l_populate_slice_a2(type, kt, ainfo, values) kt1l__populate_slice_a2(  \
	pcast(KT1L_Byte*, kt),                                         \
	(KT1L_Info){                                                   \
		.backing      = ainfo,                                     \
		.slot_size    = size_of(KT1L_Slot_Str8),                   \
		.kt_value_offset = offset_of(tmpl(KT1L_Slot,type), value), \
		.type_width   = size_of(type),                             \
		.type_name    = lit(stringify(type))                       \
	},                                                             \
	slice_byte(values), (values).len                               \
)
#pragma endregion KT1L

#pragma region Key Table 1-Layer Chained-Chunked-Cells (KT1CX)
#define def_KT1CX_Slot(type)         \
def_struct(tmpl(KT1CX_Slot,type)) {  \
	type value;                      \
	U64  key;                        \
	B32  occupied;                   \
	byte_pad(4);                     \
}
#define def_KT1CX_Cell(type, depth)      \
def_struct(tmpl(KT1CX_Cell,type)) {      \
	tmpl(KT1CX_Slot,type)  slots[depth]; \
	tmpl(KT1CX_Cell,type)* next;         \
}
#define def_KT1CX(type)                    \
def_struct(tmpl(KT1CX,type)) {             \
	tmpl(Slice_KT1CX_Cell,type) cell_pool; \
	tmpl(Slice_KT1CX_Cell,type) table;     \
} 

typedef def_struct(KT1CX_Byte_Slot) {
	U64   key;
	B32   occupied;
	byte_pad(4);
};
typedef def_struct(KT1CX_Byte_Cell) {
	Byte* next;
};
typedef def_struct(KT1CX_Byte) {
	Slice_Byte cell_pool;
	Slice_Byte table;
};
typedef def_struct(KT1CX_ByteMeta) {
	SSIZE         slot_size;
	SSIZE         slot_key_offset;
	SSIZE         cell_next_offset;
	SSIZE         cell_depth;
	SSIZE         cell_size;
	SSIZE         type_width;
	Str8          type_name;
};
typedef def_struct(KT1CX_Info) {
	AllocatorInfo backing_table;
	AllocatorInfo backing_cells;
	SSIZE         cell_pool_size;
	SSIZE         table_size;
	SSIZE         slot_size;
	SSIZE         slot_key_offset;
	SSIZE         cell_next_offset;
	SSIZE         cell_depth;
	SSIZE         cell_size;
	SSIZE         type_width;
	Str8          type_name;
};
void       kt1cx__init   (KT1CX_Info info, KT1CX_Byte* result);
void       kt1cx__clear  (KT1CX_Byte kt,  KT1CX_ByteMeta meta);
U64        kt1cx__slot_id(KT1CX_Byte kt,  U64 key, KT1CX_ByteMeta meta);
Slice_Byte kt1cx__get    (KT1CX_Byte kt,  U64 key, KT1CX_ByteMeta meta);
Slice_Byte kt1cx__set    (KT1CX_Byte kt,  U64 key, Slice_Byte value, AllocatorInfo backing_cells, KT1CX_ByteMeta meta);

#define kt1cx_assert(kt) do {   \
	slice_assert(kt.cell_pool); \
	slice_assert(kt.table);     \
} while(0)
#define kt1cx_byte(kt) (KT1CX_Byte){slice_byte(kt.cell_pool), { cast(Byte*, kt.table.ptr), kt.table.len } }
#pragma endregion KT1CX

#pragma region String Operations
inline B32 char_is_upper(U8 c) { return('A' <= c && c <= 'Z'); }
inline U8  char_to_lower(U8 c) { if (char_is_upper(c)) { c += ('a' - 'A'); } return(c); }

char* str8_to_cstr_capped(Str8 content, Slice_Byte mem);

inline U8 integer_symbols(U8 value) { 
	local_persist U8 lookup_table[16] = { '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F', }; return lookup_table[value]; 
}
Str8 str8_from_u32(AllocatorInfo ainfo, U32 num, U32 radix, U8 min_digits, U8 digit_group_separator);

typedef def_farray(Str8, 2);
typedef def_Slice(A2_Str8);
typedef def_KT1L_Slot(Str8);
typedef def_KT1L(Str8);

Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8* entries);
#define str8_fmt_backed(tbl_backing, buf_backing, fmt_template, ...) \
str8__fmt_backed(tbl_backing, buf_backing, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))

Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8* entries);
#define str8_fmt(fmt_template, ...) str8__fmt(lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))

#define Str8Cache_CELL_DEPTH 4

typedef def_KT1CX_Slot(Str8);
typedef def_KT1CX_Cell(Str8, Str8Cache_CELL_DEPTH);
typedef def_Slice(KT1CX_Cell_Str8);
typedef def_KT1CX(Str8);
typedef def_struct(Str8Cache) {
	AllocatorInfo str_reserve;
	AllocatorInfo cell_reserve;
	AllocatorInfo tbl_backing;
	KT1CX_Str8    kt;
};

typedef def_struct(Opts_str8cache_init) {
	AllocatorInfo str_reserve;
	AllocatorInfo cell_reserve;
	AllocatorInfo tbl_backing;
	SSIZE cell_pool_size;
	SSIZE table_size;
};
void      str8cache__init(Str8Cache* cache, Opts_str8cache_init* opts);
Str8Cache str8cache__make(                  Opts_str8cache_init* opts);

#define str8gen_slice_byte(gen) (Slice_Byte){ cast(Byte*, (gen).ptr), (gen).cap }

#define str8cache_init(cache, ...) str8cache__init(cache, opt_args(Opts_str8cache_init, __VA_ARGS__))
#define str8cache_make(...)        str8cache__make(       opt_args(Opts_str8cache_init, __VA_ARGS__))

void str8cache_clear(KT1CX_Str8 kt);
Str8 str8cache_get  (KT1CX_Str8 kt, U64 key);
Str8 str8cache_set  (KT1CX_Str8 kt, U64 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells);

Str8 cache_str8(Str8Cache* cache, Str8 str);

typedef def_struct(Str8Gen) {
	AllocatorInfo backing;
	UTF8*         ptr;
	SSIZE         len;
	SSIZE         cap;
};
void    str8gen_init(Str8Gen* gen, AllocatorInfo backing);
Str8Gen str8gen_make(              AllocatorInfo backing);

inline Str8 str8_from_str8gen(Str8Gen gen) { return (Str8){gen.ptr, gen.len}; }

void str8gen_append_str8(Str8Gen* gen, Str8 str);
void str8gen__append_fmt(Str8Gen* gen, Str8 fmt_template, Slice_A2_Str8* tokens);

#define str8gen_append_fmt(gen, fmt_template, ...) str8gen__append_fmt(gen, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))
#pragma endregion String Operations

#pragma region File System
typedef def_struct(FileOpInfo) {
	Slice_Byte content;
};
typedef def_struct(Opts_read_file_contents) {
	AllocatorInfo backing;
	B32           zero_backing;
	byte_pad(4);
};
void api_file_read_contents(FileOpInfo* result, Str8 path, Opts_read_file_contents opts);
void file_write_str8       (Str8 path, Str8 content);

FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents* opts);
#define file_read_contents(path, ...) file__read_contents(path, &(Opts_read_file_contents){__VA_ARGS__})
#pragma endregion File System

#pragma region WATL
typedef def_enum(U32, WATL_TokKind) {
	WATL_Tok_Space          = ' ',
	WATL_Tok_Tab            = '\t',
	WATL_Tok_CarriageReturn = '\r',
	WATL_Tok_LineFeed       = '\n',
	WATL_Tok_Text           = 0xFFFFFFFF,
};
typedef def_struct(WATL_Tok) {
	UTF8* code;
};
typedef def_Slice(WATL_Tok);
typedef def_enum(U32, WATL_LexStatus) {
	WATL_LexStatus_MemFail_SliceConstraintFail = (1 << 0),
	// WATL_LexStatus_PosUntrackable              = (1 << 1),
	// WATL_LexStatus_UnsupportedCodepoints       = (1 << 2),
	// WATL_LexStatus_MessageOverflow             = (1 << 3),
};
typedef def_struct(WATL_Pos) {
	S32 line;
	S32 column;
};
typedef def_struct(WATL_LexMsg) {
	WATL_LexMsg* next;
	Str8      content;
	WATL_Tok* tok;
	WATL_Pos  pos;
};
typedef def_struct(WATL_LexInfo) {
	WATL_LexMsg*      msgs;
	Slice_WATL_Tok    toks;
	WATL_LexStatus    signal;
	byte_pad(4);
};
typedef def_struct(Opts_watl_lex) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_toks;
	B8 failon_unsupported_codepoints;
	B8 failon_pos_untrackable;
	B8 failon_slice_constraint_fail;
	byte_pad(5);
};
void         api_watl_lex(WATL_LexInfo* info, Str8 source, Opts_watl_lex* opts);
WATL_LexInfo watl__lex   (                    Str8 source, Opts_watl_lex* opts);
#define watl_lex(source, ...) watl__lex(source, &(Opts_watl_lex){__VA_ARGS__})

typedef Str8 WATL_Node;
typedef def_Slice(WATL_Node);
typedef Slice_WATL_Node WATL_Line;
typedef def_Slice(WATL_Line);
typedef def_struct(WATL_ParseMsg) {
	WATL_ParseMsg* next;
	Str8 content;
	WATL_Line* line;
	WATL_Tok*  tok;
	WATL_Pos   pos;
};
typedef def_enum(U32, WATL_ParseStatus) {
	WATL_ParseStatus_MemFail_SliceConstraintFail = (1 << 0),
	// WATL_ParseStatus_PosUntrackable              = (1 << 1),
	// WATL_ParseStatus_UnsupportedTokens           = (1 << 2),
	// WATL_ParseStatus_MessageOverflow             = (1 << 3),
};
typedef def_struct(WATL_ParseInfo) {
	Slice_WATL_Line     lines;
	WATL_ParseMsg*      msgs;
	WATL_ParseStatus    signal;
	byte_pad(4);
};
typedef def_struct(Opts_watl_parse) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_nodes;
	AllocatorInfo ainfo_lines;
	Str8Cache*    str_cache;
	B32 failon_slice_constraint_fail;
	byte_pad(4);
};
void           api_watl_parse(WATL_ParseInfo* info, Slice_WATL_Tok tokens, Opts_watl_parse* opts);
WATL_ParseInfo watl__parse   (                      Slice_WATL_Tok tokens, Opts_watl_parse* opts);
#define watl_parse(tokens, ...) watl__parse(tokens, &(Opts_watl_parse){__VA_ARGS__})

Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines);
#pragma endregion WATL

#pragma endregion Header

#pragma region Implementation

#pragma region Memory Operations
// #include <memory.h>
void* __cdecl memcpy (void* _Dst, void const* _Src, USIZE _Size);
void* __cdecl memmove(void* _Dst, void const* _Src, USIZE _Size);
void* __cdecl memset (void* _Dst, int         _Val, USIZE _Size);

inline
SSIZE align_pow2(SSIZE x, SSIZE b) {
    assert(b != 0);
    assert((b & (b - 1)) == 0);  // Check power of 2
    return ((x + b - 1) & (~(b - 1)));
}

inline
void* memory_copy(void* restrict dest, void const* restrict src, USIZE length) {
	if (dest == nullptr || src == nullptr) { return nullptr; }
	memcpy(dest, src, length);
	return dest;
}
inline
void* memory_copy_overlapping(void* restrict dest, void const* restrict src, USIZE length) {
	if (dest == nullptr || src == nullptr) { return nullptr; }
	memmove(dest, src, length);
	return dest;
}
inline 
B32 memory_zero(void* dest, USIZE length) {
	if (dest == nullptr) return false;
	memset((unsigned char*)dest, 0, length);
	return true;
}

inline void slice__zero(Slice_Byte mem, SSIZE typewidth) { slice_assert(mem); memory_zero(mem.ptr, mem.len); }

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
	assert(ainfo.proc != nullptr);
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
void mem_rewind(AllocatorInfo ainfo, AllocatorSP save_point) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Rewind, .old_allocation = {.ptr = cast(Byte*, & save_point)}}, &(AllocatorProc_Out){});
}

inline
AllocatorSP mem_save_point(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	AllocatorProc_Out out;
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_SavePoint}, & out);
	return out.save_point;
}

inline
Slice_Byte mem__alloc(AllocatorInfo ainfo, SSIZE size, Opts_mem_alloc* opts) {
	assert(ainfo.proc != nullptr);
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
	assert(ainfo.proc != nullptr);
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

inline
Slice_Byte mem__resize(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_resize* opts) {
	assert(ainfo.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In in = {
		.data           = ainfo.data,
		.op             = mem.len < size ? AllocatorOp_Shrink : (opts->no_zero ? AllocatorOp_Grow : AllocatorOp_Grow_NoZero),
		.requested_size = size,
		.alignment      = opts->alignment,
		.old_allocation = mem,
	};
	AllocatorProc_Out out;
	ainfo.proc(in, & out);
	return out.allocation;
}

inline
Slice_Byte mem__shrink(AllocatorInfo ainfo, Slice_Byte mem, SSIZE size, Opts_mem_shrink* opts) {
	assert(ainfo.proc != nullptr);
	assert(opts != nullptr);
	AllocatorProc_In in = {
		.data           = ainfo.data,
		.op             = AllocatorOp_Shrink,
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
inline
void farena_init(FArena* arena, Slice_Byte mem) {
	assert(arena != nullptr);
	arena->start    = mem.ptr;
	arena->capacity = mem.len;
	arena->used     = 0;
}
inline FArena farena_make(Slice_Byte mem) { FArena a; farena_init(& a, mem); return a; }
inline
Slice_Byte farena__push(FArena* arena, SSIZE amount, SSIZE type_width, Opts_farena* opts) {
	assert(opts != nullptr);
	if (amount == 0) {
		return (Slice_Byte){};
	}
	SSIZE desired   = type_width * amount;
	SSIZE to_commit = align_pow2(desired, opts->alignment ?  opts->alignment : MEMORY_ALIGNMENT_DEFAULT);
	SSIZE unused    = arena->capacity - arena->used;
	assert(to_commit <= unused);
	Byte* ptr    = cast(Byte*, cast(SSIZE, arena->start) + arena->used);
	arena->used +=  to_commit;
	return (Slice_Byte){ptr, desired};
}
inline void farena_reset(FArena* arena) { arena->used = 0; }
inline
void farena_rewind(FArena* arena, AllocatorSP save_point) {
	assert(save_point.type_sig == & farena_allocator_proc);
	Byte* end = cast(Byte*, cast(SSIZE, arena->start) + arena->used);
	assert_bounds(save_point.slot, arena->start, end);
	arena->used -= save_point.slot - cast(SSIZE, arena->start);
}
inline
AllocatorSP farena_save (FArena  arena) { 
	AllocatorSP sp = { .type_sig = & farena_allocator_proc, .slot = cast(SSIZE, arena.used) }; 
	return sp; 
}
void farena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	assert(out != nullptr);
	assert(in.data != nullptr);
	FArena* arena = cast(FArena*, in.data);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation = farena__push(arena, in.requested_size, 1, &(Opts_farena){.type_name = lit("Byte"), .alignment = in.alignment});
			memory_zero(out->allocation.ptr, out->allocation.len * cast(SSIZE, in.op));
		break;

		case AllocatorOp_Free:
		break;
		case AllocatorOp_Reset:
			farena_reset(arena);
		break;

		case AllocatorOp_Grow:
		case AllocatorOp_Grow_NoZero:
		case AllocatorOp_Shrink:
			assert_msg(false, "not implemented");
		break;

		case AllocatorOp_Rewind:
			farena_rewind(arena, * cast(AllocatorSP*, in.old_allocation.ptr));
		break;
		case AllocatorOp_SavePoint:
			out->save_point = farena_save(* arena);
		break;

		case AllocatorOp_Query:
			out->features = 
			  AllocatorQuery_Alloc 
			| AllocatorQuery_Reset 
			// | AllocatorQuery_Resize 
			| AllocatorQuery_Rewind
			;
			out->max_alloc  = arena->capacity - arena->used;
			out->min_alloc  = 0;
			out->left       = out->max_alloc;
			out->save_point = farena_save(* arena);
		break;
	}
	return;
}
#pragma endregion FArena

#pragma region OS
#pragma warning(push)
#pragma warning(disable: 4820)
#pragma comment(lib, "Kernel32.lib")
#pragma comment(lib, "Advapi32.lib")
#define MS_INVALID_HANDLE_VALUE            ((MS_HANDLE)(__int64)-1)
#define MS_ANYSIZE_ARRAY                   1       
#define MS_MEM_COMMIT                      0x00001000  
#define MS_MEM_RESERVE                     0x00002000  
#define MS_MEM_LARGE_PAGES                 0x20000000  
#define MS_PAGE_READWRITE                  0x04    
#define MS_TOKEN_ADJUST_PRIVILEGES         (0x0020)
#define MS_SE_PRIVILEGE_ENABLED            (0x00000002L)
#define MS_TOKEN_QUERY                     (0x0008)
#define MS__TEXT(quote)                    L ## quote      // r_winnt
#define MS_TEXT(quote)                     MS__TEXT(quote)   // r_winnt
#define MS_SE_LOCK_MEMORY_NAME             MS_TEXT("SeLockMemoryPrivilege")
typedef int              MS_BOOL;
typedef unsigned long    MS_DWORD;
typedef MS_DWORD*        MS_PDWORD;
typedef void*            MS_HANDLE;
typedef MS_HANDLE*       MS_PHANDLE;
typedef long             MS_LONG;
typedef __int64          MS_LONGLONG;
typedef char const*      MS_LPCSTR;
typedef unsigned short*  MS_LPWSTR, *MS_PWSTR;
typedef void*            MS_LPVOID;
typedef MS_DWORD*        MS_LPDWORD;
typedef unsigned __int64 MS_ULONG_PTR, *MS_PULONG_PTR;
typedef void const*      MS_LPCVOID;
typedef struct MS_SECURITY_ATTRIBUTES *MS_PSECURITY_ATTRIBUTES, *MS_LPSECURITY_ATTRIBUTES;
typedef struct MS_OVERLAPPED          *MS_LPOVERLAPPED;
typedef def_union(MS_LARGE_INTEGER)        { struct { MS_DWORD LowPart; MS_LONG HighPart; } _; struct { MS_DWORD LowPart; MS_LONG HighPart; } u; MS_LONGLONG QuadPart; };
typedef def_struct(MS_FILE)                { void* _Placeholder; };
typedef def_struct(MS_SECURITY_ATTRIBUTES) { MS_DWORD  nLength; MS_LPVOID lpSecurityDescriptor; MS_BOOL bInheritHandle; };
typedef def_struct(MS_OVERLAPPED)          { MS_ULONG_PTR Internal; MS_ULONG_PTR InternalHigh; union { struct { MS_DWORD Offset; MS_DWORD OffsetHigh; } _; void* Pointer; } _; MS_HANDLE  hEvent; };
typedef struct MS_LUID*                    MS_PLUID;
typedef struct MS_LUID_AND_ATTRIBUTES*     MS_PLUID_AND_ATTRIBUTES;
typedef struct MS_TOKEN_PRIVILEGES*        MS_PTOKEN_PRIVILEGES;
typedef def_struct(MS_LUID)                { MS_DWORD LowPart;        MS_LONG HighPart; };
typedef def_struct(MS_LUID_AND_ATTRIBUTES) { MS_LUID  Luid;           MS_DWORD Attributes; };
typedef def_struct(MS_TOKEN_PRIVILEGES)    { MS_DWORD PrivilegeCount; MS_LUID_AND_ATTRIBUTES Privileges[MS_ANYSIZE_ARRAY]; };
__declspec(dllimport) MS_BOOL   __stdcall CloseHandle(MS_HANDLE hObject);
__declspec(dllimport) MS_BOOL   __stdcall AdjustTokenPrivileges(MS_HANDLE TokenHandle, MS_BOOL DisableAllPrivileges, MS_PTOKEN_PRIVILEGES NewState, MS_DWORD BufferLength, MS_PTOKEN_PRIVILEGES PreviousState, MS_PDWORD ReturnLength);
__declspec(dllimport) MS_HANDLE __stdcall GetCurrentProcess(void);
__declspec(dllimport) USIZE     __stdcall GetLargePageMinimum(void);
__declspec(dllimport) MS_BOOL   __stdcall LookupPrivilegeValueW(MS_LPWSTR lpSystemName, MS_LPWSTR lpName, MS_PLUID lpLuid);
__declspec(dllimport) MS_BOOL   __stdcall OpenProcessToken(MS_HANDLE ProcessHandle, MS_DWORD DesiredAccess, MS_PHANDLE TokenHandle);
__declspec(dllimport) MS_LPVOID __stdcall VirtualAlloc(MS_LPVOID lpAddress, USIZE dwSize, MS_DWORD flAllocationType, MS_DWORD flProtect);
__declspec(dllimport) MS_BOOL   __stdcall VirtualFree (MS_LPVOID lpAddress, USIZE dwSize, MS_DWORD dwFreeType);
#pragma warning(pop)

typedef def_struct(OS_Windows_State) {
	OS_SystemInfo system_info;
};
global OS_Windows_State os__windows_info;

OS_SystemInfo* os_system_info(void) {
	return & os__windows_info.system_info;
}
void os__enable_large_pages(void) {
	MS_HANDLE token;
	if (OpenProcessToken(GetCurrentProcess(), MS_TOKEN_ADJUST_PRIVILEGES | MS_TOKEN_QUERY, &token))
	{
		MS_LUID luid;
		if (LookupPrivilegeValueW(0, MS_SE_LOCK_MEMORY_NAME, &luid))
		{
			MS_TOKEN_PRIVILEGES priv;
			priv.PrivilegeCount           = 1;
			priv.Privileges[0].Luid       = luid;
			priv.Privileges[0].Attributes = MS_SE_PRIVILEGE_ENABLED;
			AdjustTokenPrivileges(token, 0, &priv, sizeof(priv), 0, 0);
		}
		CloseHandle(token);
	}
}
inline
void os_init(void) {
	os__enable_large_pages();
	OS_SystemInfo* info = & os__windows_info.system_info;
	info->target_page_size = (SSIZE)GetLargePageMinimum();
}
inline Byte* os__vmem_reserve(SSIZE size, Opts_vmem* opts) { 
	assert(opts != nullptr);
	void* result = VirtualAlloc(cast(void*, opts->base_addr), size
		,	MS_MEM_RESERVE|MS_MEM_COMMIT|(opts->no_large_pages == false ? MS_MEM_LARGE_PAGES : 0)
		,	MS_PAGE_READWRITE
	); 
	return result; 
}
inline B32 os__vmem_commit(void* vm, SSIZE size, Opts_vmem* opts) { 
	assert(opts != nullptr);
	if (opts->no_large_pages == false ) { return 1; }
	B32 result = (VirtualAlloc(vm, size, MS_MEM_COMMIT, MS_PAGE_READWRITE) != 0); 
	return result;
}
inline void  os_vmem_release(void* vm, SSIZE size) { VirtualFree(vm, 0, MS_MEM_RESERVE); }
#pragma endregion OS

#pragma region VArena (Virutal Address Space Arena)
VArena* varena__make(Opts_varena_make* opts) {
	assert(opts != nullptr);
	if (opts->reserve_size == 0) { opts->reserve_size = mega(64); }
	if (opts->commit_size  == 0) { opts->commit_size = mega(64); }
	SSIZE reserve_size   = align_pow2(opts->reserve_size, os_system_info()->target_page_size);
	SSIZE commit_size    = align_pow2(opts->commit_size,  os_system_info()->target_page_size);
	B32   no_large_pages = (opts->flags & VArenaFlag_NoLargePages) != 0;
	Byte* base           = os__vmem_reserve(reserve_size, &(Opts_vmem){.base_addr = opts->base_addr, .no_large_pages = no_large_pages});
	assert(base != nullptr);
	os_vmem_commit(base, commit_size, .no_large_pages = no_large_pages);
	SSIZE header_size = align_pow2(size_of(VArena), MEMORY_ALIGNMENT_DEFAULT);
	VArena* vm = cast(VArena*, base);
	* vm = (VArena){
		.reserve_start = cast(SSIZE, base) + header_size,
		.reserve       = reserve_size,
		.commit_size   = commit_size,
		.committed     = commit_size,
		.commit_used   = 0,
		.flags         = opts->flags
	};
	return vm;
}
Slice_Byte varena__push(VArena* vm, SSIZE amount, SSIZE type_width, Opts_varena* opts) {
	assert(amount != 0);
	SSIZE alignment      = opts->alignment ? opts->alignment : MEMORY_ALIGNMENT_DEFAULT;
	SSIZE requested_size = amount * type_width; 
	SSIZE aligned_size   = align_pow2(requested_size, alignment);
	SSIZE current_offset = vm->reserve_start + vm->commit_used;
	SSIZE to_be_used     = vm->commit_used   + aligned_size;
	SSIZE reserve_left   = vm->reserve       - current_offset;
	SSIZE header_offset  = vm->reserve_start - cast(SSIZE, vm);
	SSIZE commit_left    = vm->committed - vm->commit_used - header_offset;
	B32   exhausted      = commit_left < to_be_used;
	assert(to_be_used < reserve_left);
	if (exhausted)
	{
		SSIZE next_commit_size = reserve_left > 0 ? 
			max(vm->commit_size, to_be_used) 
		:	cast(SSIZE, align_pow2( reserve_left, os_system_info()->target_page_size));
		if (next_commit_size) {
			Byte* next_commit_start = cast(Byte*, cast(SSIZE, vm) + vm->committed);
			B32   no_large_pages    = (vm->flags & VArenaFlag_NoLargePages) != 0;
			B32   commit_result     = os_vmem_commit(next_commit_start, next_commit_size, .no_large_pages =  no_large_pages);
			if (commit_result == false) {
				return (Slice_Byte){0};
			}
			vm->committed += next_commit_size;
		}
	}
	vm->commit_used = to_be_used;
	return (Slice_Byte){.ptr = cast(Byte*, current_offset), .len = requested_size};
}
inline void varena_release(VArena* arena) { os_vmem_release(arena, arena->reserve); }
inline 
void varena_rewind(VArena* vm, AllocatorSP sp) { 
	assert(vm != nullptr); 
	assert(sp.type_sig == & varena_allocator_proc);
	vm->commit_used = sp.slot; 
}
inline AllocatorSP varena_save(VArena* vm) { return (AllocatorSP){varena_allocator_proc, vm->commit_used}; }         
void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	VArena* vm = cast(VArena*, in.data);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation = varena_push_array(vm, Byte, in.requested_size, .alignment = in.alignment);
			memory_zero(out->allocation.ptr, out->allocation.len * cast(SSIZE, in.op));
		break;

		case AllocatorOp_Free:
		break;
		case AllocatorOp_Reset:
			vm->commit_used = 0;
		break;

		case AllocatorOp_Grow_NoZero:
		case AllocatorOp_Grow: {
			SSIZE grow_amount = in.requested_size - in.old_allocation.len;
			if (grow_amount == 0) {
				out->allocation =  in.old_allocation;
				return;
			}
			SSIZE current_offset = vm->reserve_start + vm->commit_used;
			assert(in.old_allocation.ptr == cast(Byte*, current_offset));
			Slice_Byte allocation = varena_push_array(vm, Byte, grow_amount, .alignment = in.alignment);
			assert(allocation.ptr != nullptr);
			out->allocation = (Slice_Byte){ in.old_allocation.ptr, in.requested_size };
			memory_zero(out->allocation.ptr, out->allocation.len * (in.op - AllocatorOp_Grow_NoZero));
		}
		break;
		case AllocatorOp_Shrink: {
			SSIZE current_offset = vm->reserve_start + vm->commit_used;
			SSIZE shrink_amount  = in.old_allocation.len - in.requested_size;
			if (shrink_amount < 0) {
				out->allocation = in.old_allocation;
				return;
			}
			assert(in.old_allocation.ptr == cast(Byte*, current_offset));
			vm->commit_used -= shrink_amount;
			out->allocation = (Slice_Byte){ in.old_allocation.ptr, in.requested_size };
		}
		break;

		case AllocatorOp_Rewind:
			vm->commit_used = cast(SSIZE, in.old_allocation.ptr);
		break;
		case AllocatorOp_SavePoint:
			out->save_point = varena_save(vm);
		break;

		case AllocatorOp_Query:
			out->features = 
				AllocatorQuery_Alloc
			|	AllocatorQuery_Resize
			|	AllocatorQuery_Reset
			|	AllocatorQuery_Rewind
			;
			out->max_alloc  = vm->reserve - vm->committed;
			out->min_alloc  = kilo(4);
			out->left       = out->max_alloc;
			out->save_point = varena_save(vm);
		break;
	}
}
#pragma endregion VArena

#pragma region Arena (Casey-Ryan Composite Arena)
inline
Arena* arena__make(Opts_arena_make* opts) {
	assert(opts != nullptr);
	SSIZE header_size = align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT);
	VArena* current = varena__make(opts);
	assert(current != nullptr);
	Arena* arena = varena_push(current, Arena);
	* arena = (Arena){
		.backing    = current,
		.prev       = nullptr,
		.current    = arena,
		.base_pos   = 0,
		.pos        = header_size,
		.flags      = opts->flags,
	};
	return arena;
}
Slice_Byte arena__push(Arena* arena, SSIZE amount, SSIZE type_width, Opts_arena* opts) {
	assert(arena != nullptr);
	assert(opts  != nullptr);
	Arena* active        = arena->current;
	SSIZE size_requested = amount * type_width;
	SSIZE alignment      = opts->alignment ? opts->alignment : MEMORY_ALIGNMENT_DEFAULT;
	SSIZE size_aligned   = align_pow2(size_requested, alignment);
	SSIZE pos_pre        = active->pos;
	SSIZE pos_pst        = pos_pre + size_requested;
	B32 should_chain = 
		((arena->flags & ArenaFlag_NoChain) == 0)
	&&	active->backing->reserve < pos_pst;	
	if (should_chain)
	{
		Arena* new_arena = arena_make(
			.base_addr    = 0,
			.reserve_size = active->backing->reserve,
			.commit_size  = active->backing->commit_size,
			.flags        = active->backing->flags,
		);
		new_arena->base_pos = active->base_pos + active->backing->reserve;
		sll_stack_push_n(arena->current, new_arena, prev);
		active = arena->current;
	}
	Slice_Byte vresult = varena_push_array(active->backing, Byte, size_aligned, .alignment = alignment);
	slice_assert(vresult);
	assert(cast(Byte*, pos_pst) == vresult.ptr);
	active->pos = pos_pst;
	return vresult;
}
inline
void arena_release(Arena* arena) {
	assert(arena != nullptr);
	Arena* curr = arena->current; 
	Arena* prev = nullptr;
	for (; curr != nullptr;	curr = prev) {
		prev = curr->prev;
		varena_release(curr->backing);
	}
}
inline void arena_reset(Arena* arena) { arena_rewind(arena, (AllocatorSP){.type_sig = arena_allocator_proc, .slot = 0}); }
void arena_rewind(Arena* arena, AllocatorSP save_point) {
	assert(arena != nullptr);
	assert(save_point.type_sig == arena_allocator_proc);
	SSIZE header_size = align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT);
	Arena*  curr    = arena->current;	
	SSIZE   big_pos = clamp_bot(header_size, save_point.slot);
	for (Arena* prev = nullptr; curr->base_pos >= big_pos; curr = prev) {
		prev = curr->prev;
		varena_release(curr->backing);
	}
	arena->current = curr;
	SSIZE new_pos = big_pos - curr->base_pos;
	assert(new_pos <= curr->pos);
	curr->pos = new_pos;
	varena_rewind(curr->backing, (AllocatorSP){varena_allocator_proc, curr->pos});
}
inline AllocatorSP arena_save(Arena* arena) { return (AllocatorSP){arena_allocator_proc, arena->current->pos}; };
void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	assert(out != nullptr);
	Arena* arena = cast(Arena*, in.data);
	assert(arena != nullptr);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation       = arena_push_array(arena, Byte, in.requested_size, .alignment = in.alignment);
			memory_zero(out->allocation.ptr, out->allocation.len * cast(SSIZE, in.op));
		break;
		case AllocatorOp_Free:
		break;
		case AllocatorOp_Reset:
			arena_reset(arena);
		break;
		case AllocatorOp_Grow:
		case AllocatorOp_Grow_NoZero:
		case AllocatorOp_Shrink:
			assert_msg(false, "not implemented");
		break;
		case AllocatorOp_Rewind:
			arena_rewind(arena, * cast(AllocatorSP*, in.old_allocation.ptr));
		break;

		case AllocatorOp_SavePoint:
			out->save_point = arena_save(arena);
		break;
		case AllocatorOp_Query:
			out->features = 
				AllocatorQuery_Alloc
			// |	AllocatorQuery_Resize
			|	AllocatorQuery_Reset
			|	AllocatorQuery_Rewind
			;
			out->max_alloc  = arena->backing->reserve;
			out->min_alloc  = kilo(4);
			out->left       = out->max_alloc - arena->backing->commit_used;
			out->save_point = arena_save(arena);
		break;
	}
}
#pragma endregion Arena

#pragma region Key Table 1-Layer Linear (KT1L)
SSIZE kt1l__populate_slice_a2(KT1L_Byte* kt, KT1L_Info info, Slice_Byte values, SSIZE num_values ) {
	assert(kt != nullptr);
	* kt = alloc_slice(info.backing, Byte, info.slot_size * num_values );
	slice_assert(* kt);
	SSIZE num_bytes = 0;
	for (range_iter(SSIZE, iter, 0, <, num_values)) {
        SSIZE     slot_offset = iter.cursor * info.slot_size;
		Byte*     slot_cursor = & kt->ptr[slot_offset];
		Byte*     a2_cursor   = & values.ptr[iter.cursor * info.type_width * 2];

        U64*       slot_key      = (U64*)slot_cursor;
        Slice_Byte slot_value    = { slot_cursor + info.kt_value_offset, info.type_width };

		Slice_Byte a2_key        = { a2_cursor,                   info.type_width };
		Slice_Byte a2_value      = { a2_cursor + info.type_width, info.type_width };
        slice_copy(slot_value, a2_value);
		* slot_key = 0; hash64_djb8(slot_key,  a2_key);

		num_bytes += slot_value.len;
    }
	kt->len = num_values;
	return num_bytes;
}
#pragma endregion KT1l

#pragma region Key Table 1-Layer Chained-Chunked_Cells (KT1CX)
inline
void kt1cx__init(KT1CX_Info info, KT1CX_Byte* result) {
	assert(result                  != nullptr);
	assert(info.backing_cells.proc != nullptr);
	assert(info.backing_table.proc != nullptr);
	assert(info.cell_depth         >  0);
	assert(info.cell_pool_size     >= kilo(4));
	assert(info.table_size         >= kilo(4));
	assert(info.type_width         >  0);
	result->table     = mem_alloc(info.backing_table, info.table_size * info.cell_size);
	result->cell_pool = mem_alloc(info.backing_cells, info.cell_size  * info.cell_pool_size);
	result->table.len = info.table_size;
}
void kt1cx__clear(KT1CX_Byte kt, KT1CX_ByteMeta m) {
	Byte* cursor = kt.table.ptr;
	SSIZE num_cells = kt.table.len;
	kt.table.len *= m.cell_size;
	for (; cursor != slice_end(kt.table); cursor += m.cell_size )
	{
		Slice_Byte cell   = {cursor, m.cell_size};
		Slice_Byte slots  = {cell.ptr, m.cell_depth * m.slot_size };
		Byte* slot_cursor = slots.ptr;
		for (; slot_cursor < slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			Slice_Byte slot = {slot_cursor, m.slot_size};
			slice_zero(slot);
		}
		Byte* next = slot_cursor + m.cell_next_offset;
		if (next != nullptr) {
			slots.ptr   = next;
			slot_cursor = next;
			goto process_slots;
		}
	}
	kt.table.len = num_cells;
}
inline
U64 kt1cx__slot_id(KT1CX_Byte kt, U64 key, KT1CX_ByteMeta m) {
	U64 hash_index = key % cast(U64, kt.table.len * m.cell_size);
	return hash_index;
}
Slice_Byte kt1cx__get(KT1CX_Byte kt, U64 key, KT1CX_ByteMeta m) {
	U64        hash_index  = kt1cx__slot_id(kt, key, m);
	Slice_Byte cell        = { & kt.table.ptr[hash_index], m.cell_size};
	{
		Slice_Byte slots       = {cell.ptr, m.cell_depth * m.slot_size};
		Byte*      slot_cursor = slots.ptr; 
		for (; slot_cursor != slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			KT1CX_Byte_Slot* slot = cast(KT1CX_Byte_Slot*, slot_cursor + m.slot_key_offset);
			if (slot->occupied && slot->key == key) {
				Slice_Byte slot_value = {slot_cursor, m.type_width};
				return slot_value;
			}
		}
		Byte* slot_next = slot_cursor + m.cell_next_offset;
		if (slot_next != nullptr) {
			slots.ptr   = slot_next;
			slot_cursor = slot_next;
			goto process_slots;
		}
		else {
			return (Slice_Byte){0};
		}
	}
}
Slice_Byte kt1cx__set(KT1CX_Byte kt, U64 key, Slice_Byte value, AllocatorInfo backing_cells, KT1CX_ByteMeta m) {
	U64        hash_index  = kt1cx__slot_id(kt, key, m);
	Slice_Byte cell        = { & kt.table.ptr[hash_index], m.cell_size};
	{
		Slice_Byte slots       = {cell.ptr, m.cell_depth * m.slot_size};
		Byte*      slot_cursor = slots.ptr; 
		for (; slot_cursor != slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			KT1CX_Byte_Slot* slot = cast(KT1CX_Byte_Slot*, slot_cursor + m.slot_key_offset);
			if (slot->occupied == false) {
				slot->occupied = true;
				slot->key      = key;
				Slice_Byte slot_value = {slot_cursor, m.type_width};
				return slot_value;
			}
			else if (slot->key == key) {
				Slice_Byte slot_value = {slot_cursor, m.type_width};
				return slot_value;
			}
		}
		KT1CX_Byte_Cell curr_cell = { slot_cursor + m.cell_next_offset };
		if ( curr_cell.next != nullptr) {
			slots.ptr   = curr_cell.next;
			slot_cursor = curr_cell.next;
			cell.ptr    = curr_cell.next;
			goto process_slots;
		}
		else {
			Slice_Byte new_cell = mem_alloc(backing_cells, m.cell_size);
			curr_cell.next      = new_cell.ptr;
			KT1CX_Byte_Slot* slot = cast(KT1CX_Byte_Slot*, new_cell.ptr + m.slot_key_offset);
			slot->occupied = true;
			slot->key      = key;
			Slice_Byte slot_value = {new_cell.ptr, m.type_width};
			return     slot_value;
		}
	}
	assert_msg(false, "impossible path");
	return (Slice_Byte){0};
}
#pragma endregion Key Table

#pragma region String Operations
inline
char* str8_to_cstr_capped(Str8 content, Slice_Byte mem) {
	SSIZE copy_len = min(content.len, mem.len - 1);
    memory_copy(mem.ptr, content.ptr, copy_len);
    mem.ptr[copy_len] = '\0';
    return cast(char*, mem.ptr);
}
Str8 str8_from_u32(AllocatorInfo ainfo, U32 num, U32 radix, U8 min_digits, U8 digit_group_separator)
{
	Str8 result = {0};
	Str8 prefix = {0};
	switch (radix) {
		case 16: { prefix = lit("0x"); } break;
		case 8:  { prefix = lit("0o"); } break;
		case 2:  { prefix = lit("0b"); } break;
	}
	U8 digit_group_size = 3;
	switch (radix) {
		default: break;
		case 2:
		case 8:
		case 16: { 
			digit_group_size = 4;
		}
		break;
	}
	U32 needed_leading_zeros = 0;
	{
		U32 needed_digits = 1;
		{
			U32 u32_reduce = num;
			for(;;)
			{
				u32_reduce /= radix;
				if (u32_reduce == 0) {
					break;
				}
				needed_digits += 1;
			}
		}
		    needed_leading_zeros = (min_digits > needed_digits) ? min_digits - needed_digits : 0;
		U32 needed_separators    = 0;
		if (digit_group_separator != 0) 
		{
			needed_separators = (needed_digits + needed_leading_zeros) / digit_group_size;
			if (needed_separators > 0 && (needed_digits + needed_leading_zeros) % digit_group_size == 0) {
				needed_separators -= 1;
			}
		}
		result = alloc_slice(ainfo, UTF8, prefix.len + needed_leading_zeros + needed_separators + needed_digits);
		slice_assert(result);
	}
	// Fill Content
	{
		U32 num_reduce             = num;
		U32 digits_until_separator = digit_group_size;
		for (SSIZE idx = 0; idx < result.len; idx += 1)
		{
			SSIZE separator_pos = result.len - idx - 1;
			if (digits_until_separator == 0 && digit_group_separator != 0) {
				result.ptr[separator_pos] = digit_group_separator;
				digits_until_separator = digit_group_size + 1;
			}
			else {
				result.ptr[separator_pos] = char_to_lower(integer_symbols(cast(U8, num_reduce % radix)));
				num_reduce /= radix;
			}
			digits_until_separator -= 1;
			if (num_reduce == 0) {
				break;
			}
		}
		for (U32 leading_0_idx = 0; leading_0_idx < needed_leading_zeros; leading_0_idx += 1) {
			result.ptr[prefix.len + leading_0_idx] = '0';
		}
	}
	// Fill Prefix
	if (prefix.len > 0) {
		slice_copy(result, prefix);
	}
	return result;
}
Str8 str8__fmt_kt1l(AllocatorInfo ainfo, Slice_Byte buffer, KT1L_Str8 table, Str8 fmt_template)
{
	slice_assert(buffer);
	slice_assert(table);
	slice_assert(fmt_template);
	assert(ainfo.proc != nullptr ? (allocator_query(ainfo) & AllocatorQuery_Grow) != 0 : true);
	UTF8* cursor_buffer    = buffer.ptr;
	SSIZE buffer_remaining = buffer.len;

	char  curr_code  = * fmt_template.ptr;
	UTF8* cursor_fmt = fmt_template.ptr;
	SSIZE left_fmt   = fmt_template.len;
	while (left_fmt && buffer_remaining)
	{
		// Forward until we hit the delimiter '<' or the template's contents are exhausted.
		while (curr_code && curr_code != '<' && cursor_fmt != slice_end(fmt_template)) {
			* cursor_buffer = * cursor_fmt;
			++ cursor_buffer;
			++ cursor_fmt;
			-- buffer_remaining;
			-- left_fmt;
			curr_code = * cursor_fmt;
		}
		if (curr_code == '<')
		{
			UTF8* cursor_potential_token = cursor_fmt + 1;
			SSIZE potential_token_length = 0;
			B32   fmt_overflow = false;
			for (;;) {
				UTF8* cursor         = cursor_potential_token + potential_token_length;
				fmt_overflow         = cursor >= slice_end(fmt_template);
				B32 found_terminator = * (cursor_potential_token + potential_token_length) != '>';
				if (fmt_overflow || found_terminator) { break; }
				++ potential_token_length;
			}
			if (fmt_overflow) continue;
			// Hashing the potential token and cross checking it with our token table
			U64   key   = 0; hash64_djb8(& key, (Slice_Byte){ cast(void*, cursor_fmt + 1), potential_token_length});
			Str8* value = nullptr;
			for (slice_iter(table, token))
			{
				// We do a linear iteration instead of a hash table lookup because the user should be never substiuting with more than 100 unqiue tokens..
				if (token->key == key) {
					value = & token->value;
					break;
				}
			}
			if (value)
			{
				// We're going to appending the string, make sure we have enough space in our buffer.
				if (ainfo.proc != nullptr && (buffer_remaining - potential_token_length) <= 0) {
					buffer = mem_grow(ainfo, buffer, buffer.len + potential_token_length);
				}
				SSIZE left         = value->len;
				U8*   cursor_value = value->ptr;

				while (left && buffer_remaining) {
					* cursor_buffer = * cursor_value;
					++ cursor_buffer;
					++ cursor_value;
					-- buffer_remaining;
					-- left;
				}
				// Sync cursor format to after the processed token
				cursor_fmt = cursor_potential_token + potential_token_length + 1;
				curr_code  = * cursor_fmt;
				left_fmt  -= potential_token_length + 2; // The 2 here are the '<' & '>' delimiters being omitted.
				continue;
			}
			* cursor_buffer = * cursor_fmt;
			++ cursor_buffer;
			++ cursor_fmt;
			-- buffer_remaining;
			-- left_fmt;
			curr_code = * cursor_fmt;
		}
	}
	Str8   result = {buffer.ptr, buffer.len - buffer_remaining};
	return result;
}
inline
Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8* entries) {
	KT1L_Str8 kt; SSIZE num_bytes = kt1l_populate_slice_a2(Str8, kt, tbl_backing, *entries );
	SSIZE buf_size = fmt_template.len + num_bytes; buf_size = buf_size > kilo(16) ? buf_size : kilo(16);
	Slice_Byte buffer = mem_alloc(buf_backing, buf_size);
	Str8       result = str8__fmt_kt1l(buf_backing, buffer, kt, fmt_template);
	return     result;
}
Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8* entries) {
	local_persist Byte tbl_mem[kilo(32)];  FArena tbl_arena = farena_make(slice_fmem(tbl_mem));
	local_persist Byte buf_mem[kilo(128)];
	KT1L_Str8 kt = {0}; kt1l_populate_slice_a2(Str8, kt, ainfo_farena(tbl_arena), *entries );
	Str8   result = str8__fmt_kt1l((AllocatorInfo){0}, slice_fmem(buf_mem), kt, fmt_template);
	return result;
}
void str8cache__init(Str8Cache* cache, Opts_str8cache_init* opts) {
	assert(cache != nullptr);
	assert(opts != nullptr);
	assert(opts->str_reserve.proc  != nullptr);
	assert(opts->cell_reserve.proc != nullptr);
	assert(opts->tbl_backing.proc  != nullptr);
	if (opts->cell_pool_size == 0) { opts->cell_pool_size = kilo(1); }
	if (opts->table_size == 0)     { opts->table_size     = kilo(1); }
	cache->str_reserve  = opts->str_reserve;
	cache->cell_reserve = opts->cell_reserve;
	cache->tbl_backing  = opts->tbl_backing;
	KT1CX_Info info = {
		.backing_cells    = opts->cell_reserve,
		.backing_table    = opts->tbl_backing,
		.cell_pool_size   = opts->cell_pool_size,
		.table_size       = opts->table_size,
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	};
	kt1cx__init(info, cast(KT1CX_Byte*, & cache->kt));
	return;
}
inline Str8Cache str8cache__make(Opts_str8cache_init* opts) { Str8Cache cache; str8cache__init(& cache, opts); return cache; }
inline
void str8cache_clear(KT1CX_Str8 kt) {
	kt1cx_assert(kt);
	kt1cx__clear(kt1cx_byte(kt), (KT1CX_ByteMeta){
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	});
}
inline
Str8 str8cache_get(KT1CX_Str8 kt, U64 key) {
	kt1cx_assert(kt);
	Slice_Byte result = kt1cx__get(kt1cx_byte(kt), key
	,	(KT1CX_ByteMeta){
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	});
	return pcast(Str8, result);
}
inline
Str8 str8cache_set(KT1CX_Str8 kt, U64 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells) {
	kt1cx_assert(kt);
	slice_assert(value);
	assert(str_reserve.proc != nullptr);
	assert(backing_cells.proc != nullptr);
	Slice_Byte entry = kt1cx__set(kt1cx_byte(kt), key, slice_byte(value), backing_cells, (KT1CX_ByteMeta){
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	});
	slice_assert(entry);
	Str8 result  = { entry.ptr, 0 };
	B32 is_empty = (result.ptr == nullptr) && (result.len == 0);
	if (is_empty) {
		result = alloc_slice(str_reserve, UTF8, value.len);
		slice_copy(result, value);
	}
	return result;
}
inline
Str8 cache_str8(Str8Cache* cache, Str8 str) {
	assert(cache != nullptr);
	U64    key    = 0; hash64_djb8(& key, slice_byte(str));
	Str8   result = str8cache_set(cache->kt, key, str, cache->str_reserve, cache->cell_reserve);
	return result;
}

inline
void str8gen_init(Str8Gen* gen, AllocatorInfo backing) {
	assert(gen != nullptr);
	gen->backing = backing;
	gen->ptr = mem_alloc(backing, kilo(4)).ptr;
	assert(gen->ptr != nullptr);
	gen->len = 0;
	gen->cap = kilo(4);
}
inline Str8Gen str8gen_make(AllocatorInfo backing) { Str8Gen gen; str8gen_init(& gen, backing); return gen; }

inline
void str8gen_append_str8(Str8Gen* gen, Str8 str){
	Slice_Byte result = mem_grow(gen->backing, str8gen_slice_byte(* gen), str.len + gen->len);
	slice_assert(result);
	Slice_Byte to_copy = { result.ptr + gen->len, result.len - gen->len };
	slice_copy(to_copy, slice_byte(str));
	gen->ptr = cast(UTF8*, result.ptr); gen->len = result.len;
}
void str8gen__append_fmt(Str8Gen* gen, Str8 fmt_template, Slice_A2_Str8* entries){
	local_persist Byte tbl_mem[kilo(32)]; FArena tbl_arena = farena_make(slice_fmem(tbl_mem));
	KT1L_Str8 kt = {0}; kt1l_populate_slice_a2(Str8, kt, ainfo_farena(tbl_arena), *entries );
	Slice_Byte buffer = { gen->ptr + gen->len, gen->cap - gen->len };
	if (buffer.len < kilo(16)) {
		Slice_Byte result = mem_grow(gen->backing, str8gen_slice_byte(* gen), kilo(16) + gen->cap );
		slice_assert(result);
		gen->ptr = result.ptr;
		gen->cap = result.len;
		buffer = (Slice_Byte){ cast(Byte*, gen->ptr + gen->len), gen->cap - gen->len };
	}
	Str8 result = str8__fmt_kt1l(gen->backing, buffer, kt, fmt_template);
	gen->len += result.len;
}
#pragma endregion String Operations

#pragma region File System
// #include <fileapi.h>
#define MS_CREATE_ALWAYS                   2
#define MS_OPEN_EXISTING                   3
#define MS_GENERIC_READ                    (0x80000000L)
#define MS_GENERIC_WRITE                   (0x40000000L)
#define MS_FILE_SHARE_READ                 0x00000001  
#define MS_FILE_SHARE_WRITE                0x00000002  
#define MS_FILE_ATTRIBUTE_NORMAL           0x00000080  
#define MS_INVALID_FILE_SIZE               ((MS_DWORD)0xFFFFFFFF)
_declspec(dllimport) MS_HANDLE __stdcall CreateFileA(
	MS_LPCSTR                lpFileName,
	MS_DWORD                 dwDesiredAccess,
	MS_DWORD                 dwShareMode,
	MS_LPSECURITY_ATTRIBUTES lpSecurityAttributes,
	MS_DWORD                 dwCreationDisposition,
	MS_DWORD                 dwFlagsAndAttributes,
	MS_HANDLE                hTemplateFile);
_declspec(dllimport) MS_BOOL __stdcall ReadFile(
	MS_HANDLE       hFile,
	MS_LPVOID       lpBuffer,
	MS_DWORD        nNumberOfBytesToRead,
	MS_LPDWORD      lpNumberOfBytesRead,
	MS_LPOVERLAPPED lpOverlapped);
_declspec(dllimport) MS_BOOL __stdcall WriteFile(
	MS_HANDLE       hFile,
	MS_LPCVOID      lpBuffer,
	MS_DWORD        nNumberOfBytesToWrite,
	MS_LPDWORD      lpNumberOfBytesWritten,
	MS_LPOVERLAPPED lpOverlapped);
__declspec(dllimport) MS_BOOL __stdcall GetFileSizeEx(MS_HANDLE hFile, MS_LARGE_INTEGER* lpFileSize);
__declspec(dllimport) MS_DWORD __stdcall GetLastError(void);

inline
FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents* opts) {
	slice_assert(path);
    assert(opts != nullptr);
	FileOpInfo result; api_file_read_contents(& result, path, * opts);
	return result;
}
void api_file_read_contents(FileOpInfo* result, Str8 path, Opts_read_file_contents opts)
{
	assert(result != nullptr);
	slice_assert(path);
	// Backing is required at this point
	assert(opts.backing.proc != nullptr);
	// This will limit a path for V1 to be 32kb worth of codepoints.
	local_persist U8 scratch[kilo(64)];
	char const* path_cstr = str8_to_cstr_capped(path, slice_fmem(scratch) );
	MS_HANDLE id_file = CreateFileA(
		path_cstr,
		MS_GENERIC_READ,
		MS_FILE_SHARE_READ,
		nullptr,
		MS_OPEN_EXISTING,
		MS_FILE_ATTRIBUTE_NORMAL,
		nullptr
	);
	B32 open_failed = id_file == MS_INVALID_HANDLE_VALUE;
	if (open_failed) {
		MS_DWORD  error_code = GetLastError();
		assert(error_code != 0);
		return;
	}
	MS_LARGE_INTEGER file_size = {0};
	MS_DWORD get_size_failed = ! GetFileSizeEx(id_file, & file_size);
	if   (get_size_failed) {
		assert(get_size_failed == MS_INVALID_FILE_SIZE);
		return;
	}
	Slice_Byte buffer = mem_alloc(opts.backing, file_size.QuadPart);
	B32 not_enough_backing = buffer.len < file_size.QuadPart;
	if (not_enough_backing) {
		assert(not_enough_backing);
		result->content = (Slice_Byte){0};
		return;
	}
	if (opts.zero_backing) {
		slice_zero(buffer);
	}
	MS_DWORD amount_read = 0;
	MS_BOOL  read_result = ReadFile(
		id_file,
		buffer.ptr,
		cast(MS_DWORD, file_size.QuadPart),
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
void file_write_str8(Str8 path, Str8 content)
{
	slice_assert(path);
	Byte scratch[kilo(64)] = {0};
	char const* path_cstr = str8_to_cstr_capped(path, slice_fmem(scratch));
	MS_HANDLE id_file = CreateFileA(
		path_cstr,
		MS_GENERIC_WRITE,
		MS_FILE_SHARE_READ,
		nullptr,
		MS_CREATE_ALWAYS,
		MS_FILE_ATTRIBUTE_NORMAL,
		nullptr
	);
	B32 open_failed = id_file == MS_INVALID_HANDLE_VALUE;
	if (open_failed) {
		MS_DWORD  error_code = GetLastError();
		assert(error_code != 0);
		return;
	}
	MS_DWORD bytes_written = 0;
	B32 status = WriteFile(id_file
		, cast(void*, content.ptr)
		, cast(MS_DWORD, content.len)
		, & bytes_written
		, nullptr
	);
	assert(status != 0);
	assert(bytes_written == content.len);
}
#pragma endregion File System

#pragma region Debug
#if defined(BUILD_DEBUG)
// #include <stdio.h>
#define MS_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS (*__local_stdio_printf_options())
#define MS_stderr                          (__acrt_iob_func(2))
#define MS__crt_va_start_a(ap, x)          ((void)(__va_start(&ap, x)))
#define MS__crt_va_arg(ap, t)                                            \
	((sizeof(t) > sizeof(__int64) || (sizeof(t) & (sizeof(t) - 1)) != 0) \
		? **(t**)((ap += sizeof(__int64)) - sizeof(__int64))             \
		:  *(t* )((ap += sizeof(__int64)) - sizeof(__int64)))
#define MS__crt_va_end(ap)           ((void)(ap = (va_list)0))
#define va_start(ap, x)              MS__crt_va_start_a(ap, x)
#define va_arg                       MS__crt_va_arg
#define va_end                       MS__crt_va_end
#define va_copy(destination, source) ((destination) = (source))
typedef def_struct(__crt_locale_pointers) { struct __crt_locale_data* locinfo; struct __crt_multibyte_data* mbcinfo; }; 
typedef __crt_locale_pointers* _locale_t;
typedef char*                  va_list;
MS_FILE* __cdecl __acrt_iob_func(unsigned _Ix);
__declspec(noinline) __inline 
unsigned __int64* __cdecl __local_stdio_printf_options(void) {
	// NOTE(CRT): This function must not be inlined into callers to avoid ODR violations.  The
	// static local variable has different names in C and in C++ translation units.
	static unsigned __int64 _OptionsStorage; return &_OptionsStorage;
}
int __cdecl __stdio_common_vfprintf_s(
	unsigned __int64 _Options,
	MS_FILE*         _Stream,
	char const*      _Format,
	_locale_t        _Locale,
	va_list          _ArgList
);
void __cdecl __va_start(va_list* , ...);
inline
int printf_err(char const* fmt, ...) {
	int result;
	va_list args;
	va_start(args, fmt);
	result = __stdio_common_vfprintf_s(MS_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS, MS_stderr, fmt, nullptr, args);
	va_end(args);
	return result;
}
void assert_handler( char const* condition, char const* file, char const* function, S32 line, char const* msg, ... ) {
	printf_err( "%s - %s:(%d): Assert Failure: ", file, function, line );
	if ( condition )
		printf_err( "`%s` \n", condition );
	if ( msg ) {
		va_list va = {0};
		va_start( va, msg );
		__stdio_common_vfprintf_s(MS_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS, MS_stderr, msg, nullptr, va);
		va_end( va );
	}
	printf_err( "%s", "\n" );
}
#endif
#pragma endregion Debug

#pragma region WATL
void api_watl_lex(WATL_LexInfo* info, Str8 source, Opts_watl_lex* opts)
{
	if (source.len == 0) { return; }
	assert(info != nullptr);
	assert(opts != nullptr);
	assert(opts->ainfo_msgs.proc != nullptr);
	assert(opts->ainfo_toks.proc != nullptr);
	AllocatorProc_Out start_snapshot; {  opts->ainfo_toks.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & start_snapshot); }
	WATL_LexMsg* msg_last = nullptr;

	UTF8* end    = source.ptr + source.len;
	UTF8* cursor = source.ptr;
	UTF8* prev   = source.ptr - 1;
	UTF8  code   = * cursor;
	B32       was_formatting = true;
	WATL_Tok* tok            = nullptr;
	S32       num            = 0;
	for (; cursor < end;)
	{
		switch (code)
		{
			case WATL_Tok_Space:
			case WATL_Tok_Tab:
			{
				if (* prev != * cursor) {
					tok            = alloc_type(opts->ainfo_toks, WATL_Tok);
					tok->code      = cursor;
					was_formatting = true;
					++ num;
				}
				cursor += 1;
			}
			break;
			case WATL_Tok_LineFeed: {
					tok            = alloc_type(opts->ainfo_toks, WATL_Tok);
					tok->code      = cursor;
					cursor        += 1;
					was_formatting = true; 
					++ num;
			}
			break;
			// Assuming what comes after is line feed.
			case WATL_Tok_CarriageReturn: {
					tok            = alloc_type(opts->ainfo_toks, WATL_Tok);
					tok->code      = cursor;
					cursor        += 2;
					was_formatting = true; 
					++ num;
			}
			break;
			default:
			{
				if (was_formatting) {
					tok            = alloc_type(opts->ainfo_toks, WATL_Tok);
					tok->code      = cursor;
					was_formatting = false;
					++ num;
				}
				cursor += 1;
			}
			break;
		}
		prev =  cursor - 1;
		code = * cursor;
	}
	AllocatorProc_Out end_snapshot; { 
		opts->ainfo_toks.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & end_snapshot);
	}
	SSIZE num_bytes = end_snapshot.save_point.slot - start_snapshot.save_point.slot;
	if (num_bytes > start_snapshot.left) {
		info->signal |= WATL_LexStatus_MemFail_SliceConstraintFail;
		WATL_LexMsg* msg = alloc_type(opts->ainfo_msgs, WATL_LexMsg);
		assert(msg != nullptr);
		msg->pos     = (WATL_Pos){ -1, -1 };
		msg->tok     = tok;
		msg->content = lit("Token slice allocation was not contiguous");
		sll_queue_push_n(info->msgs, msg_last, msg, next);
		assert(opts->failon_slice_constraint_fail == false);
	}
	assert(tok != nullptr);
	assert(num > 0);
	info->toks.ptr = tok - num;
	info->toks.len = num;
}
WATL_LexInfo watl__lex(Str8 source, Opts_watl_lex* opts) { WATL_LexInfo info = {0}; api_watl_lex(& info, source, opts); return info; }

Str8 str8_from_watl_tok(Slice_WATL_Tok toks, WATL_Tok* tok) {
	SSIZE start    = cast(SSIZE, toks.ptr->code);
	SSIZE curr     = cast(SSIZE, tok->code);
	SSIZE offset   = curr - start;
	SSIZE left     = cast(SSIZE, toks.ptr + toks.len) - offset;
	B32   last_tok = tok == & toks.ptr[toks.len - 1]; // Check to see if this token's end is also the end of the slice:
	Str8  text     = {0};
	text.ptr = tok->code;
	text.len = last_tok ? 
		left
	// Othwerise its the next minus the curr.
	:	cast(SSIZE, (tok + 1)->code - tok->code);
	return text;
}

void api_watl_parse(WATL_ParseInfo* info, Slice_WATL_Tok tokens, Opts_watl_parse* opts)
{
	if (tokens.len == 0) { return; }
	assert(opts != nullptr);
	assert(opts->ainfo_lines.proc != nullptr);
	assert(opts->ainfo_msgs.proc != nullptr);
	assert(opts->ainfo_nodes.proc != nullptr);
	assert(opts->str_cache != nullptr);
	AllocatorProc_Out start_lines_snapshot; { opts->ainfo_lines.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & start_lines_snapshot); }
	AllocatorProc_Out start_nodes_snapshot; { opts->ainfo_nodes.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & start_nodes_snapshot); }
	WATL_ParseMsg* msg_last = nullptr;

	WATL_Line* line = alloc_type(opts->ainfo_lines, WATL_Line);
	WATL_Node* curr = alloc_type(opts->ainfo_nodes, WATL_Node);
	* curr      = (WATL_Node){0};
	* line      = (WATL_Line){ curr, 0 };
	info->lines = (Slice_WATL_Line){ line, 0 };
	for (slice_iter(tokens, token))
	{
		switch(* token->code)
		{
			case WATL_Tok_CarriageReturn:
			case WATL_Tok_LineFeed:
			{
				AllocatorProc_Out end_nodes_snapshot; { opts->ainfo_nodes.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & end_nodes_snapshot); }
				SSIZE distance_nodes = end_nodes_snapshot.save_point.slot - start_nodes_snapshot.save_point.slot;
				if (distance_nodes > start_lines_snapshot.left) {
					info->signal |= WATL_ParseStatus_MemFail_SliceConstraintFail;
					WATL_ParseMsg* msg = alloc_type(opts->ainfo_msgs, WATL_ParseMsg);
					msg->content = lit("Nodes slice allocation was not contiguous");
					msg->pos     = (WATL_Pos){cast(S32, info->lines.len), cast(S32, line->len)};
					msg->line    = line;
					msg->tok     = token;
					sll_queue_push_n(info->msgs, msg_last, msg, next);
					assert(opts->failon_slice_constraint_fail == false);
				}
				opts->ainfo_nodes.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & start_nodes_snapshot);
				WATL_Line* new_line = alloc_type(opts->ainfo_lines, WATL_Line);
				line             = new_line;
				line->ptr        = curr;
				line->len        = 0;
				info->lines.len += 1;
			}
			continue;

			default:
			break;
		}
		Str8 tok_str = str8_from_watl_tok(tokens, token);
		* curr       = cache_str8(opts->str_cache, tok_str);
		curr         = alloc_type(opts->ainfo_nodes, WATL_Node);
		* curr       = (WATL_Node){0};
		line->len   += 1;
		continue;
	}
	AllocatorProc_Out end_lines_snapshot; { opts->ainfo_lines.proc((AllocatorProc_In){.op = AllocatorOp_Query}, & end_lines_snapshot); }

	SSIZE distance_lines = end_lines_snapshot.save_point.slot - start_lines_snapshot.save_point.slot;
	if (distance_lines > start_lines_snapshot.left) {
		info->signal |= WATL_ParseStatus_MemFail_SliceConstraintFail;
		WATL_ParseMsg* msg = alloc_type(opts->ainfo_msgs, WATL_ParseMsg);
		msg->content = lit("Line slice allocation was not contiguous");
		msg->pos     = (WATL_Pos){-1, -1};
		sll_queue_push_n(info->msgs, msg_last, msg, next);
		assert(opts->failon_slice_constraint_fail == false);
		return;
	}
}
WATL_ParseInfo watl__parse(Slice_WATL_Tok tokens, Opts_watl_parse* opts) { WATL_ParseInfo info = {0}; api_watl_parse(& info, tokens, opts); return info; }

Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines)
{
	local_persist Byte scratch[kilo(64)] = {0}; FArena sarena = farena_make(slice_fmem(scratch)); AllocatorInfo sinfo = ainfo_farena(sarena);

	Str8Gen result = str8gen_make(buffer);
	U32 line_num = 0;
	for (slice_iter(lines, line))
	{
	#define fmt_entry(label, value) { lit(label), value }
		++ line_num;
		Str8 str_line_num  = str8_from_u32(sinfo, line_num,  10, 0, 0);
		Str8 str_chunk_num = str8_from_u32(sinfo, cast(U32, line->len), 10, 0, 0);
		str8gen_append_fmt(& result, "Line <line_num> - Chunks <chunk_num>:\n"
		,	fmt_entry("line_num",  str_line_num)
		,	fmt_entry("chunk_num", str_chunk_num)
		);
		for (slice_iter(* line, chunk)) 
		{
			Str8 id;
			switch (* chunk->ptr)
			{
				case WATL_Tok_Space: id = lit("Space");   break;
				case WATL_Tok_Tab:   id = lit("Tab");     break;
				default:             id = lit("Visible"); break;
			}
			Str8 str_chunk_len = str8_from_u32(sinfo, cast(U32, chunk->len), 10, 0, 0);
			str8gen_append_fmt(& result, "\t<id>(<size>): '<chunk>'\n"
			,	fmt_entry("id", id)
			,	fmt_entry("size", str_chunk_len)
			,	fmt_entry("chunk", * chunk)
			);
		}
		farena_reset(& sarena);
	#undef fmt_entry_u32
	}
	return (Str8){ result.ptr, result.len };
}
#pragma endregion WATL

#pragma endregion Implementation

#pragma warning(push)
#pragma warning(disable: 4101)
int main(void)
{
	os_init();

	VArena* vm_file = varena_make(.reserve_size = giga(4), .flags = VArenaFlag_NoLargePages);
	FileOpInfo file = file_read_contents(lit("watl.v0.msvc.c"), .backing = ainfo_varena(vm_file));
	slice_assert(file.content);

	Arena* a_msgs = arena_make();
	Arena* a_toks = arena_make();
	WATL_LexInfo lex_res = watl_lex(pcast(Str8, file.content),
		.ainfo_msgs = ainfo_arena(a_msgs),
		.ainfo_toks = ainfo_arena(a_toks),
	);
	assert((lex_res.signal & WATL_LexStatus_MemFail_SliceConstraintFail) == 0);

	Arena* str_cache_kt1_ainfo = arena_make();
	Str8Cache str_cache = str8cache_make(
		.str_reserve    = ainfo_arena(arena_make()),
		.cell_reserve   = ainfo_arena(str_cache_kt1_ainfo),
		.tbl_backing    = ainfo_arena(str_cache_kt1_ainfo),
		.cell_pool_size = kilo(4),
		.table_size     = kilo(32),
	);

	Arena* a_lines = arena_make();
	WATL_ParseInfo parse_res = watl_parse(lex_res.toks, 
		.ainfo_msgs  = ainfo_arena(a_msgs),
		.ainfo_nodes = ainfo_arena(a_toks),
		.ainfo_lines = ainfo_arena(a_lines),
		.str_cache   = & str_cache
	);
	assert((parse_res.signal & WATL_ParseStatus_MemFail_SliceConstraintFail) == 0);

	arena_reset(a_msgs);
	arena_reset(a_toks);
	Str8 listing = watl_dump_listing(ainfo_arena(a_msgs), parse_res.lines);
	return 0;
}
#pragma warning(pop)
