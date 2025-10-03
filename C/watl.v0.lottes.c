/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, LLVM & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: LLVM (2025-08-30), C-Stanard: 11

Based on: Neokineogfx - Fixing C
https://youtu.be/RrL7121MOeA
*/

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-const-variable"
#pragma clang diagnostic ignored "-Wunused-but-set-variable"
#pragma clang diagnostic ignored "-Wswitch"
#pragma clang diagnostic ignored "-Wunused-variable"
#pragma clang diagnostic ignored "-Wunknown-pragmas"
#pragma clang diagnostic ignored "-Wvarargs"
#pragma clang diagnostic ignored "-Wunused-function"
#pragma clang diagnostic ignored "-Wbraced-scalar-init"
#pragma clang diagnostic ignored "-W#pragma-messages"
#pragma clang diagnostic ignored "-Wstatic-in-inline"
#pragma clang diagnostic ignored "-Wkeyword-macro"
#pragma clang diagnostic ignored "-Wc23-compat"
#pragma clang diagnostic ignored "-Wreserved-identifier"
#pragma clang diagnostic ignored "-Wpre-c11-compat"
#pragma clang diagnostic ignored "-Wc23-extensions"
#pragma clang diagnostic ignored "-Wunused-macros"
#pragma clang diagnostic ignored "-Wdeclaration-after-statement"
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"

#pragma region Header

#pragma region DSL
#if 0
// Original macros

#define A_(x)   __attribute__((aligned (x)))
#define E_(x,y) __builtin_expect(x,y)
#define S_ static
#define I_ static inline __attribute__((always_inline))
#define N_ static        __attribute__((noinline))
#define R_            __restrict                                     
#define V_            volatile                                       
// #define W_            __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))
#endif

// Ones I'm deciding to use..

#define align_(value) __attribute__((aligned (value)))             // for easy alignment
#define expect_(x, y) __builtin_expect(x, y)                       // so compiler knows the common path
#define finline       static inline __attribute__((always_inline)) // force inline
#define noinline      static        __attribute__((noinline))      // force no inline [used in thread api]
#define R_            __restrict                                   // pointers are either restricted or volatile and nothing else 
#define V_            volatile                                     // pointers are either restricted or volatile and nothing else
// #define W_            __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))

#define glue_impl(A, B)    A ## B
#define glue(A, B)         glue_impl(A, B)
#define stringify_impl(S)  #S
#define stringify(S)       stringify_impl(S)
#define tmpl(prefix, type) prefix ## _ ## type

#define local_persist      static
#define global             static

#define static_assert      _Static_assert
#define typeof             __typeof__
#define typeof_ptr(ptr)    typeof(ptr[0])
#define typeof_same(a, b)  _Generic((a), typeof((b)): 1, default: 0)

#define def_R_(type)      type* restrict PR_ ## type
#define def_V_(type)      type* volatile PV_ ## type
#define def_ptr_set(type) def_R_(type); typedef def_V_(type)
#define def_tset(type) type; typedef def_ptr_set(type)

typedef __UINT8_TYPE__  def_tset(U1); typedef __UINT16_TYPE__ def_tset(U2); typedef __UINT32_TYPE__ def_tset(U4); typedef __UINT64_TYPE__ def_tset(U8);
typedef __INT8_TYPE__   def_tset(S1); typedef __INT16_TYPE__  def_tset(S2); typedef __INT32_TYPE__  def_tset(S4); typedef __INT64_TYPE__  def_tset(S8);
typedef unsigned char   def_tset(B1); typedef __UINT16_TYPE__ def_tset(B2); typedef __UINT32_TYPE__ def_tset(B4);
typedef float  def_tset(F4); 
typedef double def_tset(F8);
typedef float  V4_F4 __attribute__((vector_size(16)));
enum { false = 0, true  = 1, true_overflow, };

#define u1_(value) cast(U1, value)
#define u2_(value) cast(U2, value)
#define u4_(value) cast(U4, value)
#define u8_(value) cast(U8, value)
#define s1_(value) cast(S1, value)
#define s2_(value) cast(S2, value)
#define s4_(value) cast(S4, value)
#define s8_(value) cast(S8, value)
#define f4_(value) cast(F4, value)
#define f8_(value) cast(F8, value)

#define farray_len(array)                   (SSIZE)sizeof(array) / size_of( typeof((array)[0]))
#define farray_init(type, ...)              (type[]){__VA_ARGS__}
#define def_farray_impl(_type, _len)        _type A ## _len ## _ ## _type[_len]
#define def_farray(type, len)               def_farray_impl(type, len)
#define def_enum(underlying_type, symbol)   underlying_type symbol; enum   symbol
#define def_struct(symbol)                  struct symbol symbol;   struct symbol
#define def_union(symbol)                   union  symbol symbol;   union  symbol
#define def_proc(symbol)                    symbol
#define opt_args(symbol, ...)               &(symbol){__VA_ARGS__}

#define alignas                             _Alignas
#define alignof                             _Alignof
#define cast(type, data)                    ((type)(data))
#define pcast(type, data)                   * cast(type*, & (data))
#define nullptr                             cast(void*, 0)
#define offset_of(type, member)             cast(U8, & (((type*) 0)->member))
#define size_of(data)                       cast(U8, sizeof(data))

#define kilo(n)                             (cast(U8, n) << 10)
#define mega(n)                             (cast(U8, n) << 20)
#define giga(n)                             (cast(U8, n) << 30)
#define tera(n)                             (cast(U8, n) << 40)

// Signed stuff (still diff flavor from Lottes)

#define sop_1(op, a, b) cast(U1, s1_(a) op s1_(b))
#define sop_2(op, a, b) cast(U2, s2_(a) op s2_(b))
#define sop_4(op, a, b) cast(U4, s4_(a) op s4_(b))
#define sop_8(op, a, b) cast(U8, s8_(a) op s8_(b))

#define def_signed_op(id, op, width) finline U ## width id ## _s ## width(U ## width a, U ## width b) {return sop_ ## width(op, a, b); }
#define def_signed_ops(id, op)       def_signed_op(id, op, 1) def_signed_op(id, op, 2) def_signed_op(id, op, 4) def_signed_op(id, op, 8)
def_signed_ops(add, +) def_signed_ops(sub, -) def_signed_ops(mut, *) def_signed_ops(div, /)
def_signed_ops(gt,  >) def_signed_ops(lt,  <) def_signed_ops(ge, >=) def_signed_ops(le, <=)

#define def_generic_sop(op, a, ...) _Generic((a), U1:  op ## _s1, U2: op ## _s2, U4: op ## _s4, U8: op ## _s8) (a, __VA_ARGS__)
#define add_s(a,b) def_generic_sop(add,a,b)
#define sub_s(a,b) def_generic_sop(sub,a,b)
#define mut_s(a,b) def_generic_sop(mut,a,b)
#define gt_s(a,b)  def_generic_sop(gt, a,b)
#define lt_s(a,b)  def_generic_sop(lt, a,b)
#define ge_s(a,b)  def_generic_sop(ge, a,b)
#define le_s(a,b)  def_generic_sop(le, a,b)
#pragma endregion DSL

#pragma region Strings
typedef unsigned char UTF8;
typedef def_struct(Str8) { UTF8* ptr; U8 len; };
typedef Str8 Slice_UTF8;
typedef def_struct(Slice_Str8) { Str8* ptr; U8 len; };
#define lit(string_literal) (Str8){ (UTF8*) string_literal, size_of(string_literal) - 1 }
#pragma endregion Strings

#pragma region Debug
#define debug_trap()      __debugbreak()
#define assert_trap(cond) do { if (cond) __debug_trap(); } while(0)
#define assert_msg(cond, msg, ...) do { \
	if (! (cond))            \
	{                        \
		assert_handler(        \
			stringify(cond),     \
			__FILE__,            \
			__func__,            \
			cast(S4, __LINE__),  \
			msg,                 \
			## __VA_ARGS__);     \
		debug_trap();          \
	}                        \
} while(0)
void assert_handler(UTF8* condition, UTF8* file, UTF8* function, S4 line, UTF8* msg, ... );
#pragma endregion Debug

#pragma region Memory
typedef def_farray(B1, 1);
typedef def_farray(B1, 2);
typedef def_farray(B1, 4);
typedef def_farray(B1, 8);

inline U8 align_pow2(U8 x, U8 b);

#define align_struct(type_width) ((U8)(((type_width) + 7) / 8 * 8))

#define assert_bounds(point, start, end) do { \
	assert(pos_start <= pos_point); \
	assert(pos_point <= pos_end);   \
} while(0)

U8 mem_copy            (U8 dest, U8 src, U8 length);
U8 mem_copy_overlapping(U8 dest, U8 src, U8 length);
B4 mem_zero            (U8 dest, U8 length);

#define check_nil(nil, p) ((p) == 0 || (p) == nil)
#define set_nil(nil, p)   ((p) = nil)

#define sll_stack_push_n(f, n, next) do { (n)->next = (f); (f) = (n); } while(0)

#define sll_queue_push_nz(nil, f, l, n, next) \
(                           \
	check_nil(nil, f) ? (     \
		(f) = (l) = (n),        \
		set_nil(nil, (n)->next) \
	)                         \
	: (                       \
		(l)->next=(n),          \
		(l) = (n),              \
		set_nil(nil,(n)->next)  \
	)                         \
)
#define sll_queue_push_n(f, l, n, next) sll_queue_push_nz(0, f, l, n, next)

typedef def_struct(Slice_Mem) { U8 ptr; U8 len; };

#define def_Slice(type)           def_struct(tmpl(Slice,type)) { type* ptr; U8 len; }
#define slice_assert(slice)       do { assert((slice).ptr != nullptr); assert((slice).len > 0); } while(0)
#define slice_end(slice)          ((slice).ptr + (slice).len)
#define size_of_slice_type(slice) size_of( * (slice).ptr )

typedef def_Slice(void);
typedef def_Slice(B1);
#define slice_byte(slice) ((Slice_B1){cast(B1, (slice).ptr), (slice).len * size_of_slice_type(slice)})
#define slice_fmem(mem)   ((Slice_B1){ mem, size_of(mem) })

void slice__copy(Slice_B1 dest, U8 dest_typewidth, Slice_B1 src, U8 src_typewidth);
void slice__zero(Slice_B1 mem, U8 typewidth);
#define slice_copy(dest, src) do {       \
	static_assert(typeof_same(dest, src)); \
	slice__copy(slice_byte(dest),  size_of_slice_type(dest), slice_byte(src), size_of_slice_type(src)); \
} while (0)
#define slice_zero(slice) slice__zero(slice_byte(slice), size_of_slice_type(slice))

#define slice_iter(container, iter)     typeof((container).ptr) iter = (container).ptr; iter != slice_end(container); ++ iter
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) { .ptr = farray_init(type, __VA_ARGS__), .len = farray_len( farray_init(type, __VA_ARGS__)) }
#pragma endregion Memory

#pragma region Math
#define min(A, B)       (((A) < (B)) ? (A) : (B))
#define max(A, B)       (((A) > (B)) ? (A) : (B))
#define clamp_bot(X, B) max(X, B)
#pragma endregion Math

#pragma region Allocator Interface
typedef def_enum(U4, AllocatorOp) {
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
typedef def_enum(U4, AllocatorQueryFlags) {
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
typedef struct AllocatorProc_In  AllocatorProc_In;
typedef struct AllocatorProc_Out AllocatorProc_Out;
typedef struct AllocatorSP       AllocatorSP;
typedef void def_proc(AllocatorProc) (AllocatorProc_In In, U8 Out);
struct AllocatorSP {
	U8 type_sig;
	S8 slot;
};
struct AllocatorProc_In {
	U8 data;
	U8 requested_size;
	U8 alignment;
	union {
		Slice_Mem   old_allocation;
		AllocatorSP save_point;
	};
	AllocatorOp    op;
	A4_B1 _PAD_;
};
struct AllocatorProc_Out {
	union {
		Slice_Mem   allocation;
		AllocatorSP save_point;
	};
	AllocatorQueryFlags features;
	A4_B1 _PAD_;
	U8                  left; // Contiguous memory left
	U8                  max_alloc;
	U8                  min_alloc;
	B4                  continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
	A4_B1 _PAD_2;
};
typedef def_struct(AllocatorInfo) {
	AllocatorProc* proc;
	void*          data;
};
static_assert(size_of(AllocatorSP) <= size_of(Slice_Mem));
typedef def_struct(AllocatorQueryInfo) {
	AllocatorSP         save_point;
	AllocatorQueryFlags features;
	A4_B1 _PAD_;
	U8                  left; // Contiguous memory left
	U8                  max_alloc;
	U8                  min_alloc;
	B4                  continuity_break; // Whether this allocation broke continuity with the previous (address space wise)
	A4_B1 _PAD_2;
};
static_assert(size_of(AllocatorProc_Out) == size_of(AllocatorQueryInfo));

#define MEMORY_ALIGNMENT_DEFAULT (2 * size_of(void*))

AllocatorQueryInfo allocator_query(AllocatorInfo ainfo);

void        mem_free      (AllocatorInfo ainfo, Slice_Mem mem);
void        mem_reset     (AllocatorInfo ainfo);
void        mem_rewind    (AllocatorInfo ainfo, AllocatorSP save_point);
AllocatorSP mem_save_point(AllocatorInfo ainfo);

typedef def_struct(Opts_mem_alloc)  { U8 alignment; B4 no_zero; A4_B1 _PAD_; };
typedef def_struct(Opts_mem_grow)   { U8 alignment; B4 no_zero; A4_B1 _PAD_; };
typedef def_struct(Opts_mem_shrink) { U8 alignment; };
typedef def_struct(Opts_mem_resize) { U8 alignment; B4 no_zero; A4_B1 _PAD_; };

Slice_Mem mem__alloc (AllocatorInfo ainfo,                U8 size, Opts_mem_alloc*  opts);
Slice_Mem mem__grow  (AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow*   opts);
Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize* opts);
Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink* opts);

#define mem_alloc(ainfo, size, ...)       mem__alloc (ainfo,      size, opt_args(Opts_mem_alloc,  __VA_ARGS__))
#define mem_grow(ainfo,   mem, size, ...) mem__grow  (ainfo, mem, size, opt_args(Opts_mem_grow,   __VA_ARGS__))
#define mem_resize(ainfo, mem, size, ...) mem__resize(ainfo, mem, size, opt_args(Opts_mem_resize, __VA_ARGS__))
#define mem_shrink(ainfo, mem, size, ...) mem__shrink(ainfo, mem, size, opt_args(Opts_mem_shrink, __VA_ARGS__))

#define alloc_type(ainfo, type, ...)       (type*)             mem__alloc(ainfo, size_of(type),        opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ mem__alloc(ainfo, size_of(type) * num,  opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }
#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)
typedef def_struct(Opts_farena) {
	Str8 type_name;
	U8   alignment;
};
typedef def_struct(FArena) {
	U8 start;
	U8 capacity;
	U8 used;
};
typedef def_ptr_set(FArena);
FArena      farena_make  (Slice_Mem mem);
void        farena_init  (FArena*R_ arena, Slice_Mem byte);
Slice_Mem   farena__push (FArena*R_ arena, U8 amount, U8 type_width, Opts_farena* opts);
void        farena_reset (FArena*R_ arena);
void        farena_rewind(FArena*R_ arena, AllocatorSP save_point);
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
	U8 target_page_size;
};
typedef def_struct(Opts_vmem) {
	U8    base_addr;
	B4    no_large_pages;
	A4_B1 _PAD_;
};
void os_init(void);
OS_SystemInfo* os_system_info(void);

inline B4 os__vmem_commit(U8 vm, U8 size, Opts_vmem* opts);
inline U8 os__vmem_reserve(U8 size, Opts_vmem* opts);
inline void  os_vmem_release(U8 vm, U8 size);

#define os_vmem_reserve(size, ...)    os__vmem_reserve(size, opt_args(Opts_vmem, __VA_ARGS__))
#define os_vmem_commit(vm, size, ...) os__vmem_commit(vm, size, opt_args(Opts_vmem, __VA_ARGS__))
#pragma endregion OS

#pragma region VArena (Virutal Address Space Arena)
typedef Opts_farena Opts_varena;
typedef def_enum(U4, VArenaFlags) {
	VArenaFlag_NoLargePages = (1 << 0),
};
typedef def_struct(VArena) {
	U8 reserve_start;
	U8 reserve;
	U8 commit_size;
	U8 committed;
	U8 commit_used;
	VArenaFlags flags;
	A4_B1 _PAD;
};
typedef def_struct(Opts_varena_make) {
	U8 base_addr;
	U8 reserve_size;
	U8 commit_size;
	VArenaFlags flags;
	A4_B1 _PAD_;
};
VArena* varena__make(Opts_varena_make* opts);
#define varena_make(...) varena__make(opt_args(Opts_varena_make, __VA_ARGS__))

Slice_Mem   varena__push  (VArena* arena, U8 amount, U8 type_width, Opts_varena* opts);
void        varena_release(VArena* arena);
void        varena_rewind (VArena* arena, AllocatorSP save_point);
void        varena_reset  (VArena* arena);
Slice_Mem   varena__shrink(VArena* arena, Slice_Mem old_allocation, U8 requested_size, Opts_varena* opts);
AllocatorSP varena_save   (VArena* arena);

void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out);
#define ainfo_varena(varena) (AllocatorInfo) { .proc = & varena_allocator_proc, .data = varena }

#define varena_push(arena, type, ...) \
cast(type*, varena__push(arena, 1, size_of(type), opt_args(Opts_varena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define varena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ varena__push(arena, size_of(type), amount, opt_args(Opts_varena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion VArena

#pragma region Arena (Casey-Ryan Composite Arenas)
typedef Opts_varena Opts_arena;
typedef def_enum(U4, ArenaFlags) {
	ArenaFlag_NoLargePages = (1 << 0),
	ArenaFlag_NoChain      = (1 << 1),
};
typedef def_struct(Arena) {
	VArena*    backing;
	Arena*     prev;
	Arena*     current;
	U8         base_pos;
	U8         pos;
	ArenaFlags flags;
	A4_B1 _PAD_;
};
typedef Opts_varena_make Opts_arena_make;
Arena*      arena__make  (Opts_arena_make* opts);
Slice_Mem   arena__push  (Arena* arena, U8 amount, U8 type_width, Opts_arena* opts);
void        arena_release(Arena* arena);
void        arena_reset  (Arena* arena);
void        arena_rewind (Arena* arena, AllocatorSP save_point);
AllocatorSP arena_save   (Arena* arena);

void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out);
#define ainfo_arena(arena) (AllocatorInfo){ .proc = & arena_allocator_proc, .data = arena }

#define arena_make(...) arena__make(opt_args(Opts_arena_make, __VA_ARGS__))

#define arena_push(arena, type, ...) \
cast(type*, arena__push(arena, 1, size_of(type), opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define arena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ arena__push(arena, size_of(type), amount, opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion Arena

#pragma region Hashing
finline
void hash64_djb8(PR_U8 hash, Slice_Mem bytes) {
	U8 elem = bytes.ptr;
	U8 curr = hash[0];
loop:
	hash[0] <<= 8;
	hash[0]  += hash[0];
	curr     += elem;
	hash[0]   = curr;
	if (elem != bytes.ptr + bytes.len) 
	goto end;
	++ elem;
	goto loop;
end:
	return;
}
#pragma endregion Hashing

#pragma region Key Table 1-Layer Linear (KT1L)
#define def_KT1L_Slot(type)        \
def_struct(tmpl(KT1L_Slot,type)) { \
	U8   key;   \
	type value; \
}
#define def_KT1L(type)             \
	def_Slice(tmpl(KT1L_Slot,type)); \
	typedef tmpl(Slice_KT1L_Slot,type) tmpl(KT1L,type)

typedef Slice_Mem KT1L_Byte;
typedef def_struct(KT1L_Meta) {
	U8 slot_size;
	U8 kt_value_offset;
	U8 type_width;
	Str8 type_name;
};
void kt1l__populate_slice_a2(KT1L_Byte* kt, AllocatorInfo backing, KT1L_Meta m, Slice_Mem values, U8 num_values );
#define kt1l_populate_slice_a2(type, kt, ainfo, values) kt1l__populate_slice_a2(  \
	cast(KT1L_Byte*, kt),                                        \
	ainfo,                                                       \
	(KT1L_Meta){                                                 \
		.slot_size       = size_of(tmpl(KT1L_Slot,type)),          \
		.kt_value_offset = offset_of(tmpl(KT1L_Slot,type), value), \
		.type_width      = size_of(type),                          \
		.type_name       = lit(stringify(type))                    \
	},                                                           \
	slice_byte(values), (values).len                             \
)
#pragma endregion KT1L

#pragma region Key Table 1-Layer Chained-Chunked-Cells (KT1CX)
#define def_KT1CX_Slot(type)        \
def_struct(tmpl(KT1CX_Slot,type)) { \
	type value;   \
	U8  key;      \
	B4  occupied; \
	A4_B1 _PAD_;  \
}
#define def_KT1CX_Cell(type, depth)    \
def_struct(tmpl(KT1CX_Cell,type)) {    \
	tmpl(KT1CX_Slot,type)  slots[depth]; \
	tmpl(KT1CX_Cell,type)* next;         \
}
#define def_KT1CX(type)                  \
def_struct(tmpl(KT1CX,type)) {           \
	tmpl(Slice_KT1CX_Cell,type) cell_pool; \
	tmpl(Slice_KT1CX_Cell,type) table;     \
}
typedef def_struct(KT1CX_Byte_Slot) {
	U8   key;
	B4   occupied;
	A4_B1 _PAD_;
};
typedef def_struct(KT1CX_Byte_Cell) {
	U8 next;
};
typedef def_struct(KT1CX_Byte) {
	Slice_Mem cell_pool;
	Slice_Mem table;
};
typedef def_struct(KT1CX_ByteMeta) {
	U8   slot_size;
	U8   slot_key_offset;
	U8   cell_next_offset;
	U8   cell_depth;
	U8   cell_size;
	U8   type_width;
	Str8 type_name;
};
typedef def_struct(KT1CX_InfoMeta) {
	U8   cell_pool_size;
	U8   table_size;
	U8   slot_size;
	U8   slot_key_offset;
	U8   cell_next_offset;
	U8   cell_depth;
	U8   cell_size;
	U8   type_width;
	Str8 type_name;
};
typedef def_struct(KT1CX_Info) {
	AllocatorInfo backing_table;
	AllocatorInfo backing_cells;
};
void kt1cx_init   (KT1CX_Info info, KT1CX_InfoMeta m, KT1CX_Byte* result);
void kt1cx_clear  (KT1CX_Byte kt,  KT1CX_ByteMeta meta);
U8   kt1cx_slot_id(KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
U8   kt1cx_get    (KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
U8   kt1cx_set    (KT1CX_Byte kt,  U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta meta);

#define kt1cx_assert(kt) do {   \
	slice_assert(kt.cell_pool); \
	slice_assert(kt.table);     \
} while(0)
#define kt1cx_byte(kt) (KT1CX_Byte){slice_byte(kt.cell_pool), { cast(U8, kt.table.ptr), kt.table.len } }
#pragma endregion KT1CX

#pragma region String Operations
finline B4 char_is_upper(U8 c) { return('A' <= c && c <= 'Z'); }
finline U8 char_to_lower(U8 c) { if (char_is_upper(c)) { c += ('a' - 'A'); } return(c); }
inline U8 integer_symbols(U8 value) {
	local_persist U1 lookup_table[16] = { '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F', }; return lookup_table[cast(U1, value)]; 
}

char* str8_to_cstr_capped(Str8 content, Slice_Mem mem);
Str8  str8_from_u32(AllocatorInfo ainfo, U4 num, U4 radix, U8 min_digits, U8 digit_group_separator);

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
	U8 cell_pool_size;
	U8 table_size;
};
void      str8cache__init(Str8Cache* cache, Opts_str8cache_init* opts);
Str8Cache str8cache__make(                  Opts_str8cache_init* opts);

#define str8cache_init(cache, ...) str8cache__init(cache, opt_args(Opts_str8cache_init, __VA_ARGS__))
#define str8cache_make(...)        str8cache__make(       opt_args(Opts_str8cache_init, __VA_ARGS__))

void  str8cache_clear(KT1CX_Str8 kt);
U8 str8cache_get(KT1CX_Str8 kt, U8 key);
U8 str8cache_set(KT1CX_Str8 kt, U8 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells);

Str8 cache_str8(Str8Cache* cache, Str8 str);

typedef def_struct(Str8Gen) {
	AllocatorInfo backing;
	U8 ptr;
	U8 len;
	U8 cap;
};
void    str8gen_init(Str8Gen* gen, AllocatorInfo backing);
Str8Gen str8gen_make(              AllocatorInfo backing);

#define str8gen_slice_mem(gen) (Slice_mem){ cast(U8, (gen).ptr), (gen).cap }

finline Str8 str8_from_str8gen(Str8Gen gen) { return (Str8){ cast(UTF8*, gen.ptr), gen.len}; }

void str8gen_append_str8(Str8Gen* gen, Str8 str);
void str8gen__append_fmt(Str8Gen* gen, Str8 fmt_template, Slice_A2_Str8* tokens);

#define str8gen_append_fmt(gen, fmt_template, ...) str8gen__append_fmt(gen, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))
#pragma endregion String Operations

#pragma region File System
typedef def_struct(FileOpInfo) {
	Slice_Mem content;
};
typedef def_struct(Opts_read_file_contents) {
	AllocatorInfo backing;
	B4            zero_backing;
	A4_B1 _PAD_;
};
void api_file_read_contents(FileOpInfo* result, Str8 path, Opts_read_file_contents opts);
void file_write_str8       (Str8 path, Str8 content);

FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents* opts);
#define file_read_contents(path, ...) file__read_contents(path, &(Opts_read_file_contents){__VA_ARGS__})
#pragma endregion File System

#pragma endregion Header

#pragma region Implementation
#pragma endrgion Implementation

int main(void)
{
	U8 a = 4;
	U8 b = 2;
	a = add_s(a, b);
	U8 test = ge_s(a, b);
	return 0;
}

#pragma clang diagnostic pop
