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
#define r_            __restrict                                   // pointers are either restricted or volatile and nothing else 
#define v_            volatile                                     // pointers are either restricted or volatile and nothing else
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

typedef __UINT8_TYPE__  U1;
typedef __INT8_TYPE__   S1;
typedef __UINT16_TYPE__ U2;
typedef __INT16_TYPE__  S2;
typedef __UINT32_TYPE__ U4;
typedef __INT32_TYPE__  S4;
typedef __UINT64_TYPE__ U8;
typedef __INT64_TYPE__  S8;
typedef unsigned char   B1;
typedef __UINT16_TYPE__ B2;
typedef __UINT32_TYPE__ B4;
enum {
	false = 0,
	true  = 1,
	true_overflow,
};

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

// Back to lottes..

#define s1_(value) cast(S1, value)
#define s2_(value) cast(S2, value)
#define s4_(value) cast(S4, value)
#define s8_(value) cast(S8, value)

#define sop_1(op, a, b) cast(U1, s1_(a) op s1_(b))
#define sop_2(op, a, b) cast(U2, s2_(a) op s2_(b))
#define sop_4(op, a, b) cast(U4, s4_(a) op s4_(b))
#define sop_8(op, a, b) cast(U8, s8_(a) op s8_(b))

#define def_signed_op(id, op, width) finline U ## width id ## _s ## width(U ## width a, U ## width b) {return sop_ ## width(op, a, b); }
#define def_signed_ops(id, op)       def_signed_op(id, op, 1) def_signed_op(id, op, 2) def_signed_op(id, op, 4) def_signed_op(id, op, 8)
def_signed_ops(add, +) def_signed_ops(sub, -)
def_signed_ops(mut, *) def_signed_ops(div, /)
def_signed_ops(gt, >)  def_signed_ops(lt, <)
def_signed_ops(ge, >=) def_signed_ops(le, <=)

#define def_generic_sop(op, a, ...) _Generic((a), U1:  op ## _s1, U2: op ## _s2, U4: op ## _s4, U8: op ## _s8) (a, __VA_ARGS__)
#define ge_s(a,b) def_generic_sop(ge, a, b)
#define le_s(a,b) def_generic_sop(le, a, b)
#pragma region DSL

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

// TODO(Ed): Not sure about these yet..
#if 0
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
#endif
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
typedef void def_proc(AllocatorProc) (AllocatorProc_In In, AllocatorProc_Out* Out);
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
	void* start;
	U8 capacity;
	U8 used;
};
FArena      farena_make  (Slice_Mem mem);
void        farena_init  (FArena* arena, Slice_Mem byte);
Slice_Mem   farena__push (FArena* arena, U8 amount, U8 type_width, Opts_farena* opts);
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

#pragma endregion Header

#pragma region Implementation
#pragma endrgion Implementation

int main(void)
{
	U8 a = 4;
	U8 b = 2;
	U8 test = ge_s(a, b);
	return 0;
}

#pragma clang diagnostic pop
