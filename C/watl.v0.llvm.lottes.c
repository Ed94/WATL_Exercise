/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, LLVM & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: LLVM (2025-08-30), C-Stanard: 11

Following strictly (mostly): Neokineogfx - Fixing C
https://youtu.be/RrL7121MOeA

Unlike lottes_hybrid this file will be entirely untyped for any pointer addressing.
Win CRT imports will also be typeless signatures.
*/

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
#pragma clang diagnostic ignored "-Wc++-keyword"
#pragma clang diagnostic ignored "-Wimplicit-function-declaration"
#pragma clang diagnostic ignored "-Wcast-align"
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wswitch-default"
#pragma clang diagnostic ignored "-Wmissing-field-initializers"
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#pragma clang diagnostic ignored "-Wpointer-sign"

#pragma region Header

#pragma region DSL
#define A_(x)   __attribute__((aligned (x)))
#define E_(x,y) __builtin_expect(x,y)
#define S_      static
#define I_      static inline __attribute__((always_inline))
#define N_      static        __attribute__((noinline))
#define R_      __restrict
#define V_      volatile
#define W_      __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))

#define reg     register

#define glue_impl(A, B)    A ## B
#define glue(A, B)         glue_impl(A, B)
#define stringify_impl(S)  #S
#define stringify(S)       stringify_impl(S)
#define tmpl(prefix, type) prefix ## _ ## type

#define local_persist      static
#define global             static
#define internal           static

#define static_assert      _Static_assert
#define typeof             __typeof__
#define typeof_ptr(ptr)    typeof(ptr[0])
#define typeof_same(a, b)  _Generic((a), typeof((b)): 1, default: 0)

#define def_R_(type)       type*restrict type ## _R
#define def_V_(type)       type*volatile type ## _V
#define def_ptr_set(type)  def_R_(type); typedef def_V_(type)
#define def_tset(type)     type; typedef def_ptr_set(type)

/* Deviation from Lottes's Convention: Using byte-width for the with a single letter to indicating underlying type or intent.
U1:   B1
U2:   W1
U4:   I1
U8:   L1
S1:   SB1
S2:   SW1
S4:   SI1
S8:   SL1
F4:   F1
F8:   D1
F4_4: F4
*/
typedef __UINT8_TYPE__  def_tset(U1); typedef __UINT16_TYPE__ def_tset(U2); typedef __UINT32_TYPE__ def_tset(U4); typedef __UINT64_TYPE__ def_tset(U8);
typedef __INT8_TYPE__   def_tset(S1); typedef __INT16_TYPE__  def_tset(S2); typedef __INT32_TYPE__  def_tset(S4); typedef __INT64_TYPE__  def_tset(S8);
typedef unsigned char   def_tset(B1); typedef __UINT16_TYPE__ def_tset(B2); typedef __UINT32_TYPE__ def_tset(B4); typedef __UINT64_TYPE__ def_tset(B8);
typedef float           def_tset(F4); 
typedef double          def_tset(F8);
typedef float  F4_4 __attribute__((vector_size(16))); typedef def_ptr_set(F4_4);
enum { false = 0, true  = 1, true_overflow, };

#define u1_r(value) cast(U1_R, value)
#define u2_r(value) cast(U2_R, value)
#define u4_r(value) cast(U4_R, value)
#define u8_r(value) cast(U8_R, value)
#define u1_v(value) cast(U1_V, value)
#define u2_v(value) cast(U2_V, value)
#define u4_v(value) cast(U4_V, value)
#define u8_v(value) cast(U8_V, value)

#define u1_(value)  cast(U1, value)
#define u2_(value)  cast(U2, value)
#define u4_(value)  cast(U4, value)
#define u8_(value)  cast(U8, value)
#define s1_(value)  cast(S1, value)
#define s2_(value)  cast(S2, value)
#define s4_(value)  cast(S4, value)
#define s8_(value)  cast(S8, value)
#define f4_(value)  cast(F4, value)
#define f8_(value)  cast(F8, value)

#define uvar(Type, sym)                     B1 sym[sizeof(Type)]
#define farray_len(array)                   (U8)sizeof(array) / size_of( typeof((array)[0]))
#define farray_init(type, ...)              (type[]){__VA_ARGS__}
#define def_farray_sym(_type, _len)         A ## _len ## _ ## _type
#define def_farray_impl(_type, _len)        _type def_farray_sym(_type, _len)[_len]; typedef def_ptr_set(def_farray_sym(_type, _len))
#define def_farray(type, len)               def_farray_impl(type, len)
#define def_enum(underlying_type, symbol)   underlying_type def_tset(symbol); enum   symbol
#define def_struct(symbol)                  struct symbol   def_tset(symbol); struct symbol
#define def_union(symbol)                   union  symbol   def_tset(symbol); union  symbol
#define def_proc(symbol)                    symbol
#define opt_args(symbol, ...)               &(symbol){__VA_ARGS__}

#define alignas                             _Alignas
#define alignof                             _Alignof
#define cast(type, data)                    ((type)(data))
#define pcast(type, data)                   cast(type*, & (data))[0]
#define nullptr                             cast(void*, 0)
#define null                                cast(U8,    0)
#define offset_of(type, member)             cast(U8, & (((type*) 0)->member))
#define size_of(data)                       cast(U8, sizeof(data))

#define r_(ptr)                             cast(typeof_ptr(ptr)*R_, ptr)
#define v_(ptr)                             cast(typeof_ptr(ptr)*V_, ptr)
#define tr_(type, ptr)                      cast(type*R_, ptr)
#define tv_(type, ptr)                      cast(type*V_, ptr)

#define kilo(n)                             (cast(U8, n) << 10)
#define mega(n)                             (cast(U8, n) << 20)
#define giga(n)                             (cast(U8, n) << 30)
#define tera(n)                             (cast(U8, n) << 40)

//  Deviation from Lottes's Convention: Using lower snake case for the naming.

#define sop_1(op, a, b) cast(U1, s1_(a) op s1_(b))
#define sop_2(op, a, b) cast(U2, s2_(a) op s2_(b))
#define sop_4(op, a, b) cast(U4, s4_(a) op s4_(b))
#define sop_8(op, a, b) cast(U8, s8_(a) op s8_(b))

#define def_signed_op(id, op, width) I_ U ## width id ## _s ## width(U ## width a, U ## width b) {return sop_ ## width(op, a, b); }
#define def_signed_ops(id, op)       def_signed_op(id, op, 1) def_signed_op(id, op, 2) def_signed_op(id, op, 4) def_signed_op(id, op, 8)
def_signed_ops(add, +) def_signed_ops(sub, -)
def_signed_ops(mut, *) def_signed_ops(div, /)
def_signed_ops(gt,  >) def_signed_ops(lt,  <) 
def_signed_ops(ge, >=) def_signed_ops(le, <=)

#define def_generic_sop(op, a, ...) _Generic((a), U1:  op ## _s1, U2: op ## _s2, U4: op ## _s4, U8: op ## _s8) (a, __VA_ARGS__)
#define add_s(a,b) def_generic_sop(add,a,b)
#define sub_s(a,b) def_generic_sop(sub,a,b)
#define mut_s(a,b) def_generic_sop(mut,a,b)
#define gt_s(a,b)  def_generic_sop(gt, a,b)
#define lt_s(a,b)  def_generic_sop(lt, a,b)
#define ge_s(a,b)  def_generic_sop(ge, a,b)
#define le_s(a,b)  def_generic_sop(le, a,b)

I_ U4 atm_add_u4 (U4_R a, U4 v){__asm__ volatile("lock xaddl %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
I_ U8 atm_add_u8 (U8_R a, U8 v){__asm__ volatile("lock xaddq %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
I_ U4 atm_swap_u4(U4_R a, U4 v){__asm__ volatile("lock xchgl %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
I_ U8 atm_swap_u8(U8_R a, U8 v){__asm__ volatile("lock xchgq %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
 
I_ void barrier_compiler(void){__asm__ volatile("::""memory");} // Compiler Barrier
I_ void barrier_memory  (void){__builtin_ia32_mfence();}        // Memory   Barrier
I_ void barrier_read    (void){__builtin_ia32_lfence();}        // Read     Barrier
I_ void barrier_write   (void){__builtin_ia32_sfence();}        // Write    Barrier

I_ U8   clock(void){U8 aa,dd;__asm__ volatile("rdtsc":"=a"(aa),"=d"(dd));return aa;}
I_ void pause(void){__asm__ volatile("pause":::"memory");}
#pragma endregion DSL

#pragma region Strings
typedef unsigned char def_tset(UTF8);
typedef def_struct(Str8)       { U8 ptr; U8 len; }; typedef Str8 def_tset(Slice_UTF8);
typedef def_struct(Slice_Str8) { U8 ptr; U8 len; };
#define lit(string_literal)    (Str8){ u8_(string_literal), size_of(string_literal) - 1 }
#pragma endregion Strings

#pragma region Debug
#ifdef BUILD_DEBUG
#define debug_trap()      __debugbreak()
#define assert_trap(cond) do { if (cond) __debug_trap(); } while(0)
#define assert(cond)      assert_msg(cond, nullptr)
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
//  Deviation from Lottes's Convention: Don't want to mess with passing in typeless strings to the assert handler.
void assert_handler(UTF8*R_ condition, UTF8*R_ file, UTF8*R_ function, S4 line, UTF8*R_ msg, ... );
#else
#define debug_trap()
#define assert_trap(cond)
#define assert(cond)
#define assert_msg(cond, msg, ...)
#endif
#pragma endregion Debug

#pragma region Memory
typedef def_farray(B1, 1);
typedef def_farray(B1, 2);
typedef def_farray(B1, 4);
typedef def_farray(B1, 8);

I_ U8 mem_copy            (U8 dest, U8 src,   U8 len) { return (U8)(__builtin_memcpy ((void*)dest, (void const*)src,   len)); }
I_ U8 mem_copy_overlapping(U8 dest, U8 src,   U8 len) { return (U8)(__builtin_memmove((void*)dest, (void const*)src,   len)); }
I_ U8 mem_fill            (U8 dest, U8 value, U8 len) { return (U8)(__builtin_memset ((void*)dest, (int)        value, len)); }
I_ B4 mem_zero            (U8 dest,           U8 len) { if (dest == 0) return false; mem_fill(dest, 0, len); return true; }

#define struct_copy(type, dest, src) mem_copy(dest, src, sizeof(type))
#define struct_zero(type, dest)      mem_zero(dest,      sizeof(type))

I_ U8 align_pow2(U8 x, U8 b) {
    assert(b != 0);
    assert((b & (b - 1)) == 0);  // Check power of 2
    return ((x + b - 1) & (~(b - 1)));
}

#define align_struct(type_width) ((U8)(((type_width) + 7) / 8 * 8))

#define assert_bounds(point, start, end) do { \
	assert(start <= point); \
	assert(point <= end);   \
} while(0)

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

#define def_Slice(type)           def_struct(tmpl(Slice,type)) { type* ptr; U8 len; }; typedef def_ptr_set(tmpl(Slice,type))
#define slice_assert(slice)       do { assert((slice).ptr != 0); assert((slice).len > 0); } while(0)
#define slice_end(slice)          ((slice).ptr + (slice).len)
#define size_of_slice_type(slice) size_of( (slice).ptr[0] )

typedef def_struct(Slice_Mem) { U8 ptr; U8 len; };
#define slice_mem(ptr, len)   ((Slice_Mem){u8_(ptr), u8_(len)})
#define slice_mem_s(slice)    ((Slice_Mem){u8_((slice).ptr), (slice).len * size_of_slice_type(slice) })

typedef def_Slice(void);
typedef def_Slice(B1);
#define slice_to_bytes(slice) ((Slice_B1){cast(B1*, (slice).ptr), (slice).len * size_of_slice_type(slice)})
#define slice_fmem(mem)       slice_mem(u8_(mem), size_of(mem))

I_ void slice__zero(Slice_B1 mem, U8 typewidth) { slice_assert(mem); memory_zero(u8_(mem.ptr), mem.len); }
#define slice_zero(slice) slice__zero(slice_mem_s(slice), size_of_slice_type(slice))

I_ void slice__copy(Slice_B1 dest, U8 dest_typewidth, Slice_B1 src, U8 src_typewidth) {
	assert(dest.len >= src.len);
	slice_assert(dest);
	slice_assert(src);
	mem_copy(u8_(dest.ptr), u8_(src.ptr), src.len);
}
#define slice_copy(dest, src) do {       \
	static_assert(typeof_same(dest, src)); \
	slice__copy(slice_to_bytes(dest),  size_of_slice_type(dest), slice_to_bytes(src), size_of_slice_type(src)); \
} while (0)

#define slice_iter(container, iter)     (typeof((container).ptr) iter = (container).ptr; iter != slice_end(container); ++ iter)
#define slice_arg_from_array(type, ...) & (tmpl(Slice,type)) { .ptr = farray_init(type, __VA_ARGS__), .len = farray_len( farray_init(type, __VA_ARGS__)) }

#define span_iter(type, iter, m_begin, op, m_end) \
(                                   \
	tmpl(Iter_Span,type) iter = {     \
		.r      = {(m_begin), (m_end)}, \
		.cursor = (m_begin) };          \
	iter.cursor op iter.r.end;        \
	++ iter.cursor                    \
)

#define def_span(type)                                                \
	        def_struct(tmpl(     Span,type)) { type begin; type end; }; \
	typedef def_struct(tmpl(Iter_Span,type)) { tmpl(Span,type) r; type cursor; }

typedef def_span(B1);
typedef def_span(U4);
typedef def_span(U8);
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
typedef struct AllocatorProc_In  def_tset(AllocatorProc_In);
typedef struct AllocatorProc_Out def_tset(AllocatorProc_Out);
typedef struct AllocatorSP       AllocatorSP;
typedef void def_proc(AllocatorProc) (U8 data, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out);
struct AllocatorSP {
	AllocatorProc* type_sig;
	U8             slot;
};
struct AllocatorProc_In {
	U8 data;
	U8 requested_size;
	U8 alignment;
	union {
		Slice_Mem   old_allocation;
		AllocatorSP save_point;
	};
	AllocatorOp   op;
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
	A4_B1 _PAD_2;
};
typedef def_struct(AllocatorInfo) {
	AllocatorProc* proc;
	U8             data;
};
static_assert(size_of(AllocatorSP) <= size_of(Slice_Mem));
typedef def_struct(AllocatorQueryInfo) {
	AllocatorSP         save_point;
	AllocatorQueryFlags features;
	A4_B1 _PAD_;
	U8                  left; // Contiguous memory left
	U8                  max_alloc;
	U8                  min_alloc;
	A4_B1 _PAD_2;
};
static_assert(size_of(AllocatorProc_Out) == size_of(AllocatorQueryInfo));

#define MEMORY_ALIGNMENT_DEFAULT (2 * size_of(void*))

I_ void allocator_query__u(U8 ainfo_proc, U8 ainfo_data, U8 allocator_query_info);

I_ void mem_free__u      (U8 proc, U8 data, U8 mem_ptr, U8 mem_len);
I_ void mem_reset__u     (U8 proc, U8 data);
I_ void mem_rewind__u    (U8 proc, U8 data, U8 sp_type_sig, U8 sp_slot);
I_ void mem_save_point__u(U8 proc, U8 data, U8 sp);

I_ AllocatorQueryInfo allocator_query(AllocatorInfo ainfo);

I_ void        mem_free      (AllocatorInfo ainfo, Slice_Mem mem);
I_ void        mem_reset     (AllocatorInfo ainfo);
I_ void        mem_rewind    (AllocatorInfo ainfo, AllocatorSP save_point);
I_ AllocatorSP mem_save_point(AllocatorInfo ainfo);

I_ void mem__alloc__u (U8 out_mem, U8 proc, U8 data,                         U8 size, U8 alignemnt, B4 no_zero);
I_ void mem__grow__u  (U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment, B4 no_zero, B4 give_actual);
I_ void mem__resize__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment, B4 no_zero, B4 give_actual);
I_ void mem__shrink__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment);

typedef def_struct(Opts_mem_alloc)  { U8 alignment; B4 no_zero; A4_B1 _PAD_; };
typedef def_struct(Opts_mem_grow)   { U8 alignment; B4 no_zero; B4 give_actual; };
typedef def_struct(Opts_mem_resize) { U8 alignment; B4 no_zero; B4 give_actual; };
typedef def_struct(Opts_mem_shrink) { U8 alignment; };

I_ Slice_Mem mem__alloc (AllocatorInfo ainfo,                U8 size, Opts_mem_alloc_R  opts);
I_ Slice_Mem mem__grow  (AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow_R   opts);
I_ Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize_R opts);
I_ Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink_R opts);

#define mem_alloc(ainfo, size, ...)       mem__alloc (ainfo,      size, opt_args(Opts_mem_alloc,  __VA_ARGS__))
#define mem_grow(ainfo,   mem, size, ...) mem__grow  (ainfo, mem, size, opt_args(Opts_mem_grow,   __VA_ARGS__))
#define mem_resize(ainfo, mem, size, ...) mem__resize(ainfo, mem, size, opt_args(Opts_mem_resize, __VA_ARGS__))
#define mem_shrink(ainfo, mem, size, ...) mem__shrink(ainfo, mem, size, opt_args(Opts_mem_shrink, __VA_ARGS__))

#define alloc_type(ainfo, type, ...)       (type*)                    mem__alloc(ainfo, size_of(type),        opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ (type*)mem__alloc(ainfo, size_of(type) * num,  opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }
#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)
typedef def_struct(Opts_farena) {
	U8 alignment;
};
typedef def_struct(FArena) {
	U8 start;
	U8 capacity;
	U8 used;
};

I_ void farena_init__u  (U8 arena, U8 mem_ptr, U8 mem_len);
   void farena__push__u (U8 arena, U8 amount, U8 type_width, U8 alignment, U8 slice_mem);
I_ void farena_reset__u (U8 arena);
I_ void farena_rewind__u(U8 arena, U8 sp_type_sig, U8 sp_slot);
I_ void farena_save__u  (U8 arena, U8 sp);

I_ FArena      farena_make  (Slice_Mem mem);
I_ void        farena_init  (FArena_R arena, Slice_Mem byte);
I_ Slice_Mem   farena__push (FArena_R arena, U8 amount, U8 type_width, Opts_farena*R_ opts);
I_ void        farena_reset (FArena_R arena);
I_ void        farena_rewind(FArena_R arena, AllocatorSP save_point);
I_ AllocatorSP farena_save  (FArena  arena);

void farena_allocator_proc(U8 data, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out);
#define ainfo_farena(arena) (AllocatorInfo){ .proc = farena_allocator_proc, .data = u8_(& arena) }

#define farena_push_mem(arena, amount, ...) farena__push(arena, amount, 1, opt_args(Opts_farena, lit(stringify(B1)), __VA_ARGS__))

#define farena_push(arena, type, ...) \
cast(type*, farena__push(arena, size_of(type), 1, opt_args(Opts_farena, __VA_ARGS__))).ptr

#define farena_push_array(arena, type, amount, ...) \
(Slice ## type){ farena__push(arena, size_of(type), amount, opt_args(Opts_farena, __VA_ARGS__)).ptr, amount }
#pragma endregion FArena

#pragma endregion Header

#pragma region Implementation

#pragma region Allocator Interface
I_ void allocator_query__u(U8 ainfo_proc, U8 ainfo_data, U8 allocator_query_info) {
	assert(ainfo_proc != null); 
	cast(AllocatorProc*, ainfo_proc)(ainfo_data, 0, 0, 0, 0, AllocatorOp_Query, allocator_query_info); 
}
I_ void mem_free__u(U8 proc, U8 data, U8 mem_ptr, U8 mem_len) {
	assert(proc != null); 
	cast(AllocatorProc*, proc)(data, 0, 0, mem_ptr, mem_len, AllocatorOp_Free, 0);
}
I_ void mem_reset__u(U8 proc, U8 data) {
	assert(proc != null);
	cast(AllocatorProc*, proc)(data, 0, 0, 0, 0, AllocatorOp_Reset, 0);
}
I_ void mem_rewind__u(U8 proc, U8 data, U8 sp_type_sig, U8 sp_slot) { 
	assert(proc != null);
	cast(AllocatorProc*, proc)(data, 0, 0, sp_type_sig, sp_slot, AllocatorOp_Rewind, 0);
}
I_ void mem_save_point__u(U8 proc, U8 data, U8 sp) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0}; 
	cast(AllocatorProc*, proc)(data, 0, 0, 0, 0, AllocatorOp_SavePoint, u8_(out));
	struct_copy(AllocatorSP, sp, (U8) out + offset_of(AllocatorProc_Out, save_point));
}
I_ void mem__alloc__u(U8 out_mem, U8 proc, U8 data, U8 size, U8 alignment, B4 no_zero) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0};
	cast(AllocatorProc*, proc)(data, size, alignment, 0, 0, no_zero ? AllocatorOp_Alloc_NoZero : AllocatorOp_Alloc, u8_(out));
	struct_copy(Slice_Mem, out_mem, (U8) out + offset_of(AllocatorProc_Out, allocation));
}
I_ void mem__grow__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment, B4 no_zero, B4 give_actual) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0};
	cast(AllocatorProc*, proc)(data, size, alignment, old_ptr, old_len, no_zero ? AllocatorOp_Grow_NoZero : AllocatorOp_Grow, u8_(out));
	if (give_actual == false) { u8_r(out + offset_of(AllocatorProc_Out, allocation) + offset_of(Slice_Mem, len))[0] = size; }
	struct_copy(Slice_Mem, out_mem, (U8) out + offset_of(AllocatorProc_Out, allocation));
}
I_ void mem__shrink__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0};
	cast(AllocatorProc*, proc)(data, size, alignment, old_ptr, old_len, AllocatorOp_Shrink, u8_(out));
	struct_copy(Slice_Mem, out_mem, (U8) out + offset_of(AllocatorProc_Out, allocation));
}
I_ void mem__resize__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment, B4 no_zero, B4 give_acutal) { 
	if (old_len == size) { struct_copy(Slice_Mem, out_mem, (U8)& slice_mem(old_ptr, old_len)); }
	if (old_len <  size) { mem__grow__u  (out_mem, proc, data, old_ptr, old_len, size, alignment, no_zero, give_acutal); }
	else                 { mem__shrink__u(out_mem, proc, data, old_ptr, old_len, size, alignment); }
}

I_ AllocatorQueryInfo allocator_query(AllocatorInfo ainfo) { AllocatorQueryInfo out; allocator_query__u(u8_(ainfo.proc), ainfo.data, u8_(& out)); return out; }

I_ void mem_free  (AllocatorInfo ainfo, Slice_Mem mem)          { mem_free__u  (u8_(ainfo.proc), ainfo.data, mem.ptr, mem.len); }
I_ void mem_reset (AllocatorInfo ainfo)                         { mem_reset__u (u8_(ainfo.proc), ainfo.data); }
I_ void mem_rewind(AllocatorInfo ainfo, AllocatorSP save_point) { mem_rewind__u(u8_(ainfo.proc), ainfo.data, u8_(save_point.type_sig), save_point.slot); }

I_ AllocatorSP mem_save_point(AllocatorInfo ainfo) { AllocatorSP sp; mem_save_point__u(u8_(ainfo.proc), ainfo.data, u8_(& sp)); return sp; }

I_ Slice_Mem mem__alloc(AllocatorInfo ainfo, U8 size, Opts_mem_alloc_R opts) { 
	assert(opts != nullptr); Slice_Mem result; 
	mem__alloc__u(u8_(& result), u8_(ainfo.proc), ainfo.data, size, opts->alignment, opts->no_zero); 
	return result; 
}
I_ Slice_Mem mem__grow(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow_R opts) {
	assert(opts != nullptr);
	Slice_Mem out; mem__grow__u(u8_(& out), u8_(ainfo.proc), ainfo.data, mem.ptr, mem.len, size, opts->alignment, opts->no_zero, opts->give_actual);
	if (!opts->give_actual) { out.len = size; }
	return out;
}
I_ Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize_R opts) {
	assert(opts != nullptr);
	Slice_Mem out; mem__resize__u(u8_(& out), u8_(ainfo.proc), ainfo.data, mem.ptr, mem.len, size, opts->alignment, opts->no_zero, opts->give_actual);
	return out;
}
I_ Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink_R opts) {
	assert(opts != nullptr);
	Slice_Mem out; mem__shrink__u(u8_(& out), u8_(ainfo.proc), ainfo.data, mem.ptr, mem.len, size, opts->alignment);
	return out;
}
#pragma endregion Allocator Interface

#pragma region FArena (Fixed-Sized Arena)
I_ void farena_init__u(U8 arena, U8 mem_ptr, U8 mem_len) {
	assert(arena != null);
	u8_r(arena + offset_of(FArena, start)   )[0] = mem_ptr;
	u8_r(arena + offset_of(FArena, capacity))[0] = mem_len;
	u8_r(arena + offset_of(FArena, used)    )[0] = 0;
}
inline void farena__push__u(U8 arena, U8 amount, U8 type_width, U8 alignment, U8 result) {
	if (amount == 0) { struct_zero(Slice_Mem, result); }
	U8   reg desired   = type_width * amount;
	U8   reg to_commit = align_pow2(desired, alignment ?  alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8_R reg used      = u8_r(arena + offset_of(FArena, used));
	U8   reg unused    = u8_r(arena + offset_of(FArena, capacity))[0] - used[0]; assert(to_commit <= unused);
	U8   reg ptr       = u8_r(arena + offset_of(FArena, start)   )[0] + used[0];
	used[0] += to_commit;
	struct_copy(Slice_Mem, result, (U8)& slice_mem(ptr, desired));
}
inline void farena__grow__u(U8 result, U8 arena, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment, B4 should_zero) {
	assert(result != null);
	assert(arena  != null);
	U8_R reg used = u8_r(arena + offset_of(FArena, used));
	/*Check if the allocation is at the end of the arena*/{
		U8 reg alloc_end = old_ptr + old_len;
		U8 reg arena_end = u8_r(arena + offset_of(FArena, start))[0] + used[0];
		if (alloc_end != arena_end) {
			// Not at the end, can't grow in place
			struct_zero(Slice_Mem, result);
			return;
		}
	}
	// Calculate growth
	U8 reg grow_amount  = requested_size - old_len;
	U8 reg aligned_grow = align_pow2(grow_amount, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8 reg unused       = u8_r(arena + offset_of(FArena, capacity))[0] - used[0];
	if (aligned_grow > unused) {
		// Not enough space
		struct_zero(Slice_Mem, result);
		return;
	}
	used[0] += aligned_grow;
	struct_copy(Slice_Mem, result, (U8)& slice_mem(old_ptr, aligned_grow + requested_size));
	memory_zero(old_ptr + old_len, grow_amount * cast(U8, should_zero));
}
inline void farena__shrink__u(U8 result, U8 arena, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment) {
	assert(result != null);
	assert(arena  != null);
	U8_R reg used = u8_r(arena + offset_of(FArena, used));
	/*Check if the allocation is at the end of the arena*/ {
		U8 reg alloc_end = old_ptr + old_len;
		U8 reg arena_end = u8_r(arena + offset_of(FArena, start))[0] + used[0];
		if (alloc_end != arena_end) {
			// Not at the end, can't shrink but return adjusted size
			struct_copy(Slice_Mem, result, (U8)& slice_mem(old_ptr, requested_size));
			return;
		}
	}
	U8 reg aligned_original = align_pow2(old_len, MEMORY_ALIGNMENT_DEFAULT);
	U8 reg aligned_new      = align_pow2(requested_size, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	used[0] -= (aligned_original - aligned_new);
	struct_copy(Slice_Mem, result, (U8)& slice_mem(old_ptr, requested_size));
}
I_ void farena_reset__u(U8 arena) { u8_r(arena + offset_of(FArena, used))[0] = 0; }
I_ void farena_rewind__u(U8 arena, U8 sp_type_sig, U8 sp_slot) {
	assert(sp_type_sig == (U8)& farena_allocator_proc);
	U8   reg start = u8_r(arena + offset_of(FArena, start))[0];
	U8_R reg used  = u8_r(arena + offset_of(FArena, used));
	U8   reg end   = start + used[0]; assert_bounds(sp_slot, start, end);
	used[0] -= sp_slot - start;
}
I_ void farena_save__u(U8 arena, U8 sp) {
	u8_r(sp + offset_of(AllocatorSP, type_sig))[0] = (U8)& farena_allocator_proc;
	u8_r(sp + offset_of(AllocatorSP, slot    ))[0] = u8_r(arena + offset_of(FArena, used))[0];
}
void farena_allocator_proc(U8 arena, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out)
{
	assert(out   != null);
	assert(arena != null);
	U8 reg allocation = arena + offset_of(AllocatorProc_Out, allocation);
	switch (op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			farena__push__u(arena, requested_size, 1, alignment, allocation);
			memory_zero(u8_r(allocation + offset_of(Slice_Mem, ptr))[0], u8_r(allocation + offset_of(Slice_Mem, len))[0] * op);
		break;
		case AllocatorOp_Free:                       break;
		case AllocatorOp_Reset: farena_reset__u(arena); break;

		case AllocatorOp_Grow:
		case AllocatorOp_Grow_NoZero:
			farena__grow__u(allocation, arena, old_ptr, old_len, requested_size, alignment, op - AllocatorOp_Grow_NoZero);
		break;
		case AllocatorOp_Shrink:
			farena__shrink__u(allocation, arena, old_ptr, old_len, requested_size, alignment);
		break;

		case AllocatorOp_Rewind:    farena_rewind__u(arena, old_ptr, old_len); break;
		case AllocatorOp_SavePoint: farena_save__u(arena, allocation);         break;

		case AllocatorOp_Query:
			u4_r(out + offset_of(AllocatorQueryInfo, features))[0] =
			  AllocatorQuery_Alloc
			| AllocatorQuery_Reset
			| AllocatorQuery_Resize
			| AllocatorQuery_Rewind
			;
			U8 reg max_alloc = u8_r(arena + offset_of(FArena, capacity))[0] - u8_r(arena + offset_of(FArena, used))[0];
			u8_r(out + offset_of(AllocatorQueryInfo, max_alloc))[0] = max_alloc;
			u8_r(out + offset_of(AllocatorQueryInfo, min_alloc))[0] = 0;
			u8_r(out + offset_of(AllocatorQueryInfo, left     ))[0] = max_alloc;
			farena_save__u(arena, out + offset_of(AllocatorQueryInfo, save_point));
		break;
	}
	return;
}
#pragma endregion FArena

#pragma endregion Implementation

int main(void)
{
	return 0;
}

#pragma clang diagnostic pop
