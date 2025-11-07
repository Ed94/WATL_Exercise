/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, LLVM & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: LLVM (2025-08-30), C-Stanard: 11

Following strictly: Neokineogfx - Fixing C
https://youtu.be/RrL7121MOeA
*/

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wpre-c11-compat"
// #pragma clang diagnostic ignored "-Wc++-keyword"
#pragma clang diagnostic ignored "-Wcast-qual"
// #pragma clang diagnostic ignored "-Wunused-constvariable"
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
#pragma clang diagnostic ignored "-Wc23-extensions"
#pragma clang diagnostic ignored "-Wunused-macros"
#pragma clang diagnostic ignored "-Wdeclaration-after-statement"
#pragma clang diagnostic ignored "-Wunsafe-buffer-usage"
#pragma clang diagnostic ignored "-Wimplicit-function-declaration"
#pragma clang diagnostic ignored "-Wcast-align"
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wswitch-default"
#pragma clang diagnostic ignored "-Wmissing-field-initializers"
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#pragma clang diagnostic ignored "-Wpointer-sign"

#pragma region Header

#pragma region DSL
#define LP_ static
#define G_  static

#define A_(x)   __attribute__((aligned (x)))
#define E_(x,y) __builtin_expect(x,y)
#define S_      static
#define I_      S_ inline __attribute__((always_inline))
#define N_      S_        __attribute__((noinline))
#define R_      __restrict
#define V_      volatile
#define W_      __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))

// #define reg     register

#define glue_impl(A, B)    A ## B
#define glue(A, B)         glue_impl(A, B)
#define stringify_impl(S)  #S
#define stringify(S)       cast(UTF8*, stringify_impl(S))
#define tmpl(prefix, type) prefix ## _ ## type

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
#define def_field(s,member)                 tmpl(s,member) = __builtin_offsetof(s,member) // Used within enum blocks
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
#define offset_of(type, member)             cast(U8,__builtin_offsetof(type,member))
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
#define def_field_str8(member) def_field(Str8,member)
enum {
	def_field_str8(ptr),
	def_field_str8(len),
};
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
			(UTF8*)__FILE__,     \
			(UTF8*)__func__,     \
			cast(S4, __LINE__),  \
			msg,                 \
			## __VA_ARGS__);     \
		debug_trap();          \
	}                        \
} while(0)
//  Deviation from Lottes's Convention: Don't want to mess with passing in typeless strings to the assert handler.
S_ void assert_handler(UTF8*R_ condition, UTF8*R_ file, UTF8*R_ function, S4 line, UTF8*R_ msg, ... );
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

#define struct_assign(type, dest, src) cast(type*R_, dest)[0] = cast(type*R_, src)[0]

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
enum {
	Slice_ptr = offset_of(Slice_Mem, ptr),
	Slice_len = offset_of(Slice_Mem, len),
};
#define slice_mem(ptr, len)   ((Slice_Mem){u8_(ptr), u8_(len)})
#define slice_mem_s(slice)    ((Slice_Mem){u8_((slice).ptr), (slice).len * size_of_slice_type(slice) })

typedef def_Slice(void);
typedef def_Slice(B1);
#define slice_to_bytes(slice) ((Slice_B1){cast(B1*, (slice).ptr), (slice).len * size_of_slice_type(slice)})
#define slice_fmem(mem)       slice_mem(u8_(mem), size_of(mem))

I_ void slice__zero(Slice_B1 mem, U8 typewidth) { slice_assert(mem); mem_zero(u8_(mem.ptr), mem.len); }
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

I_ void slice_assign(U8 dest, U8 src) {
	u8_r(dest + Slice_ptr)[0] = u8_r(src + Slice_ptr)[0];
	u8_r(dest + Slice_len)[0] = u8_r(src + Slice_len)[0];
}
I_ void slice_assign_comp(U8 dest, U8 ptr, U8 len) {
	u8_r(dest + Slice_ptr)[0] = ptr;
	u8_r(dest + Slice_len)[0] = len;
}
I_ void slice_clear(U8 base) {
	u8_r(base + Slice_ptr)[0] = 0;
	u8_r(base + Slice_len)[0] = 0;
}

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
typedef struct AllocatorProc_Out def_tset(AllocatorProc_Out);
typedef struct AllocatorSP       AllocatorSP;
typedef void def_proc(AllocatorProc) (U8 data, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out);
struct AllocatorSP {
	AllocatorProc* type_sig;
	U8             slot;
};
enum {
	def_field(AllocatorSP,type_sig),
	def_field(AllocatorSP,slot),
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
enum {
	def_field(AllocatorProc_Out,allocation),
	def_field(AllocatorProc_Out,save_point),
	def_field(AllocatorProc_Out,features),
	def_field(AllocatorProc_Out,left),
	def_field(AllocatorProc_Out,max_alloc),
	def_field(AllocatorProc_Out,min_alloc),
};
typedef def_struct(AllocatorInfo) {
	AllocatorProc* proc;
	U8             data;
};
static_assert(size_of(AllocatorSP) <= size_of(Slice_Mem));
enum {
	def_field(AllocatorInfo,proc),
	def_field(AllocatorInfo,data),
};
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
enum {
	def_field(AllocatorQueryInfo,save_point),
	def_field(AllocatorQueryInfo,features),
	def_field(AllocatorQueryInfo,left),
	def_field(AllocatorQueryInfo,max_alloc),
	def_field(AllocatorQueryInfo,min_alloc),
};

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

#define alloc_type(ainfo, type, ...)       (type*)                    mem__alloc(ainfo, size_of(type),       opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ (type*)mem__alloc(ainfo, size_of(type) * num, opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }
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
enum {
	def_field(FArena,start),
	def_field(FArena,capacity),
	def_field(FArena,used),
};

I_ void farena_init__u  (U8 arena, U8 mem_ptr, U8 mem_len);
S_ void farena__push__u (U8 arena, U8 amount, U8 type_width, U8 alignment, U8 slice_addr);
I_ void farena_reset__u (U8 arena);
I_ void farena_rewind__u(U8 arena, U8 sp_slot);
I_ void farena_save__u  (U8 arena, U8 sp);

S_ U8          farena_make__u (U8 mem_slice);
I_ FArena      farena_make   (Slice_Mem mem);
I_ void        farena_init   (FArena_R arena, Slice_Mem byte);
S_ Slice_Mem   farena__push  (FArena_R arena, U8 amount, U8 type_width, Opts_farena*R_ opts);
I_ void        farena_reset  (FArena_R arena);
I_ void        farena_rewind (FArena_R arena, AllocatorSP save_point);
I_ AllocatorSP farena_save   (FArena  arena);

S_ void farena_allocator_proc(U8 data, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out);
#define ainfo_farena(arena) (AllocatorInfo){ .proc = farena_allocator_proc, .data = u8_(& arena) }

#define farena_push_mem(arena, amount, ...) farena__push(arena, amount, 1, opt_args(Opts_farena, lit(stringify(B1)), __VA_ARGS__))

#define farena_push(arena, type, ...) \
cast(type*, farena__push(arena, size_of(type), 1, opt_args(Opts_farena, __VA_ARGS__))).ptr

#define farena_push_array(arena, type, amount, ...) \
(Slice ## type){ farena__push(arena, size_of(type), amount, opt_args(Opts_farena, __VA_ARGS__)).ptr, amount }
#pragma endregion FArena

#pragma region OS
typedef def_struct(OS_SystemInfo)    { U8 target_page_size; };
typedef def_struct(Opts_vmem)        { U8 base_addr; B4 no_large_pages; A4_B1 _PAD_; };
typedef def_struct(OS_Windows_State) { OS_SystemInfo system_info; }; 
enum { 
	def_field(OS_SystemInfo,target_page_size),
	def_field(Opts_vmem,base_addr),
	def_field(Opts_vmem,no_large_pages),
	def_field(OS_Windows_State,system_info),
};
G_ OS_Windows_State os__windows_info;

I_ U8   os_system_info(void);
S_ void os_init       (void);

I_ U8   os_vmem_reserve__u(       U8 size, B4 no_large_pages, U8 base_addr);
I_ B4   os_vmem_commit__u (U8 vm, U8 size, B4 no_large_pages);
I_ void os_vmem_release__u(U8 vm, U8 size);

I_ U8   os__vmem_reserve(       U8 size, Opts_vmem_R opts);
I_ B4   os__vmem_commit (U8 vm, U8 size, Opts_vmem_R opts);
I_ void os_vmem_release (U8 vm, U8 size);

#define os_vmem_commit(vm, size, ...) os__vmem_commit (vm, size, opt_args(Opts_vmem, __VA_ARGS__))
#define os_vmem_reserve(size, ...)    os__vmem_reserve(    size, opt_args(Opts_vmem, __VA_ARGS__))
#pragma endregion OS

#pragma region VArena (Virtual Address Space Arena)
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
};
enum {
	def_field(VArena,reserve_start),
	def_field(VArena,reserve),
	def_field(VArena,commit_size),
	def_field(VArena,committed),
	def_field(VArena,commit_used),
	def_field(VArena,flags),
};
typedef def_struct(Opts_varena_make) {
	U8 base_addr;
	U8 reserve_size;
	U8 commit_size;
	VArenaFlags flags;
};
enum {
	def_field(Opts_varena_make,base_addr),
	def_field(Opts_varena_make,reserve_size),
	def_field(Opts_varena_make,commit_size),
	def_field(Opts_varena_make,flags),
};

S_ U8   varena__make__u  (U8 reserve_size, U8 commit_size, U4 flags, U8 base_addr);
I_ void varena_release__u(U8 arena);
I_ void varena_reset__u  (U8 arena);
I_ void varena_rewind__u (U8 arena,  U8 sp_slot);
I_ void varena_save__u   (U8 arena,  U8 sp_addr);
S_ void varena__push__u  (U8 arena,  U8 amount, U8 type_width, U8 alignment, U8 slice_addr);
S_ void varena__grow__u  (U8 result, U8 arena,  U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment, B4 should_zero);
S_ void varena__shrink__u(U8 result, U8 arena,  U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment);

I_ VArena*      varena__make  (Opts_varena_make*R_ opts);
I_ Slice_Mem    varena__push  (VArena_R arena, U8 amount, U8 type_width, Opts_varena*R_ opts);
I_ void         varena_release(VArena_R arena);
I_ void         varena_reset  (VArena_R arena);
I_ void         varena_rewind (VArena_R arena, AllocatorSP save_point);
I_ Slice_Mem    varena__shrink(VArena_R arena, Slice_Mem old_allocation, U8 requested_size, Opts_varena*R_ opts);
I_ AllocatorSP  varena_save   (VArena_R arena);

#define varena_make(...) varena__make(opt_args(Opts_varena_make, __VA_ARGS__))

S_ void varena_allocator_proc(U8 data, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out);

#define ainfo_varena(arena) (AllocatorInfo){ .proc = varena_allocator_proc, .data = u8_(arena) }

#define varena_push_mem(arena, amount, ...) varena__push(arena, amount, 1, opt_args(Opts_varena, __VA_ARGS__))

#define varena_push(arena, type, ...) \
cast(type*, varena__push(arena, size_of(type), 1, opt_args(Opts_varena, __VA_ARGS__)).ptr)

#define varena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ varena__push(arena, size_of(type), amount, opt_args(Opts_varena, __VA_ARGS__)).ptr, amount }
#pragma endregion VArena

#pragma region Arena
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
enum {
	def_field(Arena,backing),
	def_field(Arena,prev),
	def_field(Arena,current),
	def_field(Arena,base_pos),
	def_field(Arena,pos),
	def_field(Arena,flags),
};

S_ U8   arena_make__u   (U8 reserve_size, U8 commit_size, U4 flags, U8 base_addr);
S_ void arena__push__u  (U8 arena, U8 amount, U8 type_width, U8 alignemnt, U8 out_mem);
I_ void arena_release__u(U8 arena);
I_ void arena_reset__u  (U8 arena);
S_ void arena_rewind__u (U8 arena, U8 slot);
I_ void arena_save__u   (U8 arena, U8 out_sp);

typedef Opts_varena_make Opts_arena_make;
S_ Arena*      arena__make  (Opts_arena_make*R_ opts);
S_ Slice_Mem   arena__push  (Arena_R arena, U8 amount, U8 type_width, Opts_arena*R_ opts);
I_ void        arena_release(Arena_R arena);
I_ void        arena_reset  (Arena_R arena);
S_ void        arena_rewind (Arena_R arena, AllocatorSP save_point);
I_ AllocatorSP arena_save   (Arena_R arena);

S_ void arena_allocator_proc(U8 data, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out);
#define ainfo_arena(arena) (AllocatorInfo){ .proc = & arena_allocator_proc, .data = u8_(arena) }

#define arena_make(...) arena__make(opt_args(Opts_arena_make, __VA_ARGS__))

#define arena_push_mem(arena, amount, ...) arena__push(arena, amount, 1, opt_args(Opts_arena, lit(stringify(B1)), __VA_ARGS__))

#define arena_push(arena, type, ...) \
cast(type*, arena__push(arena, 1, size_of(type), opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define arena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ arena__push(arena, size_of(type), amount, opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion Arena

#pragma region Hashing
I_ void hash64_fnv1a__u(U8 hash, U8 data_ptr, U8 data_len, U8 seed) {
	LP_ U8 const default_seed = 0xcbf29ce484222325; 
	if (seed != 0) { u8_r(hash)[0] = seed; }
	else           { u8_r(hash)[0] = default_seed; }
	U8 elem = data_ptr;
loop:
	if (elem == data_ptr + data_len) goto end;
	u8_r(hash)[0] ^= u1_r(elem)[0];
	u8_r(hash)[0] *= 0x100000001b3;
	elem += 1;
	goto loop;
end: 
	return;
}
typedef def_struct(Opts_hash64_fnv1a) { U8 seed; };
I_ void hash64__fnv1a(U8_R hash, Slice_Mem data, Opts_hash64_fnv1a*R_ opts) {
	assert(opts != nullptr);
	hash64_fnv1a__u(u8_(hash), data.ptr, data.len, opts->seed);
}
#define hash64_fnv1a(hash, data, ...) hash64__fnv1a(hash, data, opt_args(Opts_hash64_fnv1a, __VA_ARGS__))
#pragma endregion Hashing

#pragma region Key Table Linear (KTL)
#define def_KTL_Slot(type)        \
def_struct(tmpl(KTL_Slot,type)) { \
	U8   key;   \
	type value; \
}
#define def_KTL(type)             \
	def_Slice(tmpl(KTL_Slot,type)); \
	typedef tmpl(Slice_KTL_Slot,type) tmpl(KTL,type)

enum {
	KTL_Slot_key   = 0,
	KTL_Slot_value = 8,
};

typedef Slice_Mem  KTL_Byte;
typedef def_struct(KTL_Meta) {
	U8   slot_size;
	U8   kt_value_offset;
	U8   type_width;
	Str8 type_name;
};

typedef def_farray(Str8, 2);
typedef def_Slice(A2_Str8);
typedef def_KTL_Slot(Str8);
typedef def_KTL(Str8);
I_ void ktl_populate_slice_a2_str8(U8 kt, U8 backing_proc, U8 backing_data, U8 values);
#pragma endregion KTL

#pragma region Key Table 1-Layer Chained-Chunked-Cells (KT1CX)
#define def_KT1CX_Slot(type)        \
def_struct(tmpl(KT1CX_Slot,type)) { \
	type value;    \
	U8   key;      \
	B4   occupied; \
	A4_B1 _PAD_;   \
}
#define def_KT1CX_Cell(type, depth)    \
def_struct(tmpl(KT1CX_Cell,type)) {    \
	tmpl(KT1CX_Slot,type)  slots[depth]; \
	tmpl(KT1CX_Slot,type)* next;         \
}
#define def_KT1CX(type)              \
def_struct(tmpl(KT1CX,type)) {       \
	tmpl(Slice_KT1CX_Cell,type) table; \
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
enum {
	def_field(KT1CX_Byte_Slot,key),
	def_field(KT1CX_Byte_Slot,occupied),

	def_field(KT1CX_ByteMeta,slot_size),
	def_field(KT1CX_ByteMeta,slot_key_offset),
	def_field(KT1CX_ByteMeta,cell_next_offset),
	def_field(KT1CX_ByteMeta,cell_depth),
	def_field(KT1CX_ByteMeta,cell_size),
	def_field(KT1CX_ByteMeta,type_width),
	def_field(KT1CX_ByteMeta,type_name),

	def_field(KT1CX_InfoMeta,cell_pool_size),
	def_field(KT1CX_InfoMeta,table_size),
	def_field(KT1CX_InfoMeta,slot_size),
	def_field(KT1CX_InfoMeta,slot_key_offset),
	def_field(KT1CX_InfoMeta,cell_next_offset),
	def_field(KT1CX_InfoMeta,cell_depth),
	def_field(KT1CX_InfoMeta,cell_size),
	def_field(KT1CX_InfoMeta,type_width),
	def_field(KT1CX_InfoMeta,type_name),
};
S_ void kt1cx_init__u   (U8 backing_tbl, U8 backing_cells, U8 m, U8 result);
S_ void kt1cx_clear__u  (U8 kt, U8 m);
I_ U8   kt1cx_slot_id__u(U8 kt, U8 key);
S_ U8   kt1cx_get__u    (U8 kt, U8 key, U8 m);
S_ U8   kt1cx_set__u    (U8 kt, U8 key, U8 v_ptr, U8 v_len, U8 backing_cells, U8 m);

I_ void kt1cx_init   (KT1CX_Info info, KT1CX_InfoMeta m, KT1CX_Byte*R_ result);
I_ void kt1cx_clear  (KT1CX_Byte kt,          KT1CX_ByteMeta meta);
I_ U8   kt1cx_slot_id(KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
I_ U8   kt1cx_get    (KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
I_ U8   kt1cx_set    (KT1CX_Byte kt,  U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta meta);

#define kt1cx_assert(kt) do { \
	slice_assert(kt.table);     \
} while(0)
#define kt1cx_byte(kt) (KT1CX_Byte){ (Slice_Mem){u8_(kt.table.ptr), kt.table.len} }
#pragma endregion KT1CX

#pragma region String Operations
I_ B4 char_is_upper(U1 c);
I_ U1 char_to_lower(U1 c);
I_ U1 integer_symbols(U1 value);

I_ char* str8_to_cstr_capped(Str8 content, Slice_Mem mem);
I_ Str8  str8_from_u32(AllocatorInfo ainfo, U4 num, U4 radix, U4 min_digits, U4 digit_group_separator);

#define Str8Cache_CELL_DEPTH 4

typedef def_KT1CX_Slot(Str8);
typedef def_KT1CX_Cell(Str8, Str8Cache_CELL_DEPTH);
typedef def_Slice(KT1CX_Cell_Str8);
typedef def_KT1CX(Str8);
enum {
	def_field(KT1CX_Str8,table),

	def_field(KT1CX_Slot_Str8,value),
	def_field(KT1CX_Slot_Str8,key),
	def_field(KT1CX_Slot_Str8,occupied),
};

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
	U8            cell_pool_size;
	U8            table_size;
};
enum {
	def_field(Str8Cache,str_reserve),
	def_field(Str8Cache,cell_reserve),
	def_field(Str8Cache,tbl_backing),
	def_field(Str8Cache,kt),

	def_field(Opts_str8cache_init,str_reserve),
	def_field(Opts_str8cache_init,cell_reserve),
	def_field(Opts_str8cache_init,tbl_backing),
	def_field(Opts_str8cache_init,cell_pool_size),
	def_field(Opts_str8cache_init,table_size),
};

S_ void str8cache__fill_byte_meta__u(U8 meta);
S_ void str8cache__fill_info_meta__u(U8 meta, U8 cell_pool_size, U8 table_size);

S_ U8   str8_to_cstr_capped__u(U8 str_slice, U8 mem_slice);
S_ void str8_from_u32__u(U8 result, U8 ainfo_proc, U8 ainfo_data, U4 num, U4 radix, U4 min_digits, U4 digit_group_separator);
S_ void str8__fmt_ktl__u(U8 result, U8 ainfo_proc, U8 ainfo_data, U8 buffer_slice, U8 table_slice, U8 fmt_slice);
S_ void str8__fmt_backed__u(U8 result, U8 tbl_backing_proc, U8 tbl_backing_data, U8 buf_backing_proc, U8 buf_backing_data, U8 fmt_slice, U8 entries_slice);
S_ void str8__fmt__u(U8 result, U8 fmt_slice, U8 entries_slice);

I_ Str8 str8__fmt_ktl(AllocatorInfo ainfo, Slice_Mem*R_ buffer, KTL_Str8 table, Str8 fmt_template);
I_ Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8*R_ entries);
I_ Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8*R_ entries);

S_ void str8cache__init__u(U8 cache, U8 opts);
S_ void str8cache_clear__u(U8 kt);
S_ U8   str8cache_get__u(U8 kt, U8 key);
S_ U8   str8cache_set__u(U8 kt, U8 key, U8 value_str, U8 str_reserve, U8 backing_cells);
S_ void cache_str8__u(U8 result, U8 cache, U8 str);

I_ void      str8cache__init(Str8Cache_R cache, Opts_str8cache_init*R_ opts);
I_ Str8Cache str8cache__make(Opts_str8cache_init*R_ opts);
I_ void      str8cache_clear(KT1CX_Str8 kt);
I_ Str8*     str8cache_get  (KT1CX_Str8 kt, U8 key);
I_ Str8*     str8cache_set  (KT1CX_Str8 kt, U8 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells);
I_ Str8      cache_str8     (Str8Cache_R cache, Str8 str);

typedef def_struct(Str8Gen) {
	AllocatorInfo backing;
	UTF8*         ptr;
	U8            len;
	U8            cap;
};
enum {
	def_field(Str8Gen,backing),
	def_field(Str8Gen,ptr),
	def_field(Str8Gen,len),
	def_field(Str8Gen,cap),
};

S_ void str8gen_init__u(U8 gen, U8 backing);
S_ void str8gen_append_str8__u(U8 gen, U8 str);
S_ void str8gen__append_fmt__u(U8 gen, U8 fmt_slice, U8 entries_slice);

I_ void    str8gen_init(Str8Gen_R gen, AllocatorInfo backing);
I_ Str8Gen str8gen_make(               AllocatorInfo backing);
#define str8gen_slice_mem(gen) slice_mem_s(gen)

I_ Str8    str8_from_str8gen(Str8Gen gen);
I_ void    str8gen_append_str8(Str8Gen_R gen, Str8 str);
I_ void    str8gen__append_fmt(Str8Gen_R gen, Str8 fmt_template, Slice_A2_Str8*R_ entries);
#define str8gen_append_fmt(gen, fmt_template, ...) str8gen__append_fmt(gen, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))
#pragma endregion String Operations

#pragma region File System
#define FILE_PATH_SCRATCH_CAP kilo(64)
typedef def_struct(FileOpInfo) {
	Slice_Mem content;
};
typedef def_struct(Opts_read_file_contents) {
	AllocatorInfo backing;
	B4            zero_backing;
	A4_B1 _PAD_;
};
enum {
	def_field(FileOpInfo,content),
	def_field(Opts_read_file_contents,backing),
	def_field(Opts_read_file_contents,zero_backing),
};

S_ void file_read_contents__u(U8 path_ptr, U8 path_len, U8 backing_proc, U8 backing_data, B4 zero_backing, U8 result);
I_ FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents*R_ opts);
#define file_read_contents(path, ...) file__read_contents(path, opt_args(Opts_read_file_contents, __VA_ARGS__))

S_ void file_write_str8__u(U8 path_ptr, U8 path_len, U8 content_ptr, U8 content_len);
I_ void file_write_str8(Str8 path, Str8 content);
#pragma endregion FIle System

#pragma region WATL
#define WATL_Tok_Space          ' '
#define WATL_Tok_Tab            '\t'
#define WATL_Tok_CarriageReturn '\r'
#define WATL_Tok_LineFeed       '\n'
#define WATL_Tok_Text           0x0FFFFFFF

typedef Str8 def_tset(WATL_Tok);
typedef def_Slice(WATL_Tok);

typedef def_enum(U4, WATL_LexStatus) {
	WATL_LexStatus_MemFail_SliceConstraintFail = (1 << 0),
};
typedef def_struct(WATL_Pos) {
	U4 line;
	U4 column;
};
typedef def_struct(WATL_LexMsg) {
	WATL_LexMsg* next;
	Str8         content;
	WATL_Tok*    tok;
	WATL_Pos     pos;
};
typedef def_struct(WATL_LexInfo) {
	WATL_LexMsg*   msgs;
	Slice_WATL_Tok toks;
	WATL_LexStatus signal;
	A4_B1 _PAD_;
};
typedef def_struct(Opts_watl_lex) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_toks;
	B1 failon_unsupported_codepoints;
	B1 failon_pos_untrackable;
	B1 failon_slice_constraint_fail;
	A4_B1 _PAD_;
};

typedef WATL_Tok  WATL_Node;
typedef def_ptr_set(WATL_Node);
typedef def_Slice(WATL_Node);
typedef Slice_WATL_Node def_tset(WATL_Line);
typedef def_Slice(WATL_Line);
typedef def_struct(WATL_ParseMsg) {
	WATL_ParseMsg* next;
	Str8           content;
	WATL_Line*     line;
	WATL_Tok*      tok;
	WATL_Pos       pos;
};
typedef def_enum(U4, WATL_ParseStatus) {
	WATL_ParseStatus_MemFail_SliceConstraintFail = (1 << 0),
};
typedef def_struct(WATL_ParseInfo) {
	Slice_WATL_Line  lines;
	WATL_ParseMsg*   msgs;
	WATL_ParseStatus signal;
	A4_B1 _PAD_;
};
typedef def_struct(Opts_watl_parse) {
	AllocatorInfo ainfo_msgs;
	AllocatorInfo ainfo_nodes;
	AllocatorInfo ainfo_lines;
	Str8Cache*    str_cache;
	B4            failon_slice_constraint_fail;
	A4_B1 _PAD_;
};
enum {
	def_field(WATL_Pos,line),
	def_field(WATL_Pos,column),

	def_field(WATL_LexMsg,next),
	def_field(WATL_LexMsg,content),
	def_field(WATL_LexMsg,tok),
	def_field(WATL_LexMsg,pos),

	def_field(WATL_LexInfo,msgs),
	def_field(WATL_LexInfo,toks),
	def_field(WATL_LexInfo,signal),

	def_field(Opts_watl_lex,ainfo_msgs),
	def_field(Opts_watl_lex,ainfo_toks),
	def_field(Opts_watl_lex,failon_unsupported_codepoints),
	def_field(Opts_watl_lex,failon_pos_untrackable),
	def_field(Opts_watl_lex,failon_slice_constraint_fail),

	def_field(WATL_ParseMsg,next),
	def_field(WATL_ParseMsg,content),
	def_field(WATL_ParseMsg,line),
	def_field(WATL_ParseMsg,tok),
	def_field(WATL_ParseMsg,pos),

	def_field(WATL_ParseInfo,lines),
	def_field(WATL_ParseInfo,msgs),
	def_field(WATL_ParseInfo,signal),

	def_field(Opts_watl_parse,ainfo_msgs),
	def_field(Opts_watl_parse,ainfo_nodes),
	def_field(Opts_watl_parse,ainfo_lines),
	def_field(Opts_watl_parse,str_cache),
	def_field(Opts_watl_parse,failon_slice_constraint_fail),
};

S_ void watl_lex__u  (U8 info, U8 source, U8 opts);
S_ void watl_parse__u(U8 info, U8 tokens, U8 opts);
S_ void watl_dump_listing__u(U8 result, U8 buffer_ainfo, U8 lines);

I_ void         api_watl_lex(WATL_LexInfo_R info, Str8 source, Opts_watl_lex*R_ opts);
I_ WATL_LexInfo watl__lex   (                     Str8 source, Opts_watl_lex*R_ opts);
I_ void         api_watl_parse(WATL_ParseInfo_R info, Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts);
I_ WATL_ParseInfo watl__parse(Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts);
I_ Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines);
#pragma endregion WATL

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
	struct_assign(AllocatorSP, sp, (U8) out + AllocatorProc_Out_save_point);
}
I_ void mem__alloc__u(U8 out_mem, U8 proc, U8 data, U8 size, U8 alignment, B4 no_zero) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0};
	cast(AllocatorProc*, proc)(data, size, alignment, 0, 0, no_zero ? AllocatorOp_Alloc_NoZero : AllocatorOp_Alloc, u8_(out));
	slice_assign(out_mem, (U8) out + AllocatorProc_Out_allocation);
}
I_ void mem__grow__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment, B4 no_zero, B4 give_actual) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0};
	cast(AllocatorProc*, proc)(data, size, alignment, old_ptr, old_len, no_zero ? AllocatorOp_Grow_NoZero : AllocatorOp_Grow, u8_(out));
	if (give_actual == false) { u8_r(out + AllocatorProc_Out_allocation + Slice_len)[0] = size; }
	slice_assign(out_mem, (U8) out + AllocatorProc_Out_allocation);
}
I_ void mem__shrink__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment) {
	assert(proc != null);
	uvar(AllocatorProc_Out, out) = {0};
	cast(AllocatorProc*, proc)(data, size, alignment, old_ptr, old_len, AllocatorOp_Shrink, u8_(out));
	slice_assign(out_mem, (U8) out + AllocatorProc_Out_allocation);
}
I_ void mem__resize__u(U8 out_mem, U8 proc, U8 data, U8 old_ptr, U8 old_len, U8 size, U8 alignment, B4 no_zero, B4 give_acutal) { 
	if (old_len == size) { slice_assign_comp(out_mem, old_ptr, old_len); }
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
	u8_r(arena + FArena_start   )[0] = mem_ptr;
	u8_r(arena + FArena_capacity)[0] = mem_len;
	u8_r(arena + FArena_used    )[0] = 0;
}
S_ inline void farena__push__u(U8 arena, U8 amount, U8 type_width, U8 alignment, U8 result) {
	if (amount == 0) { slice_clear(result); }
	U8   desired   = type_width * amount;
	U8   to_commit = align_pow2(desired, alignment ?  alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8_R used      = u8_r(arena + FArena_used);
	U8   unused    = u8_r(arena + FArena_capacity)[0] - used[0]; assert(to_commit <= unused);
	U8   ptr       = u8_r(arena + FArena_start   )[0] + used[0];
	used[0] += to_commit;
	slice_assign_comp(result, ptr, desired);
}
S_ inline void farena__grow__u(U8 result, U8 arena, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment, B4 should_zero) {
	assert(result != null);
	assert(arena  != null);
	U8_R used = u8_r(arena + FArena_used);
	/*Check if the allocation is at the end of the arena*/{
		U8 alloc_end = old_ptr + old_len;
		U8 arena_end = u8_r(arena + FArena_start)[0] + used[0];
		if (alloc_end != arena_end) {
			// Not at the end, can't grow in place
			slice_clear(result);
			return;
		}
	}
	// Calculate growth
	U8 grow_amount  = requested_size - old_len;
	U8 aligned_grow = align_pow2(grow_amount, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8 unused       = u8_r(arena + FArena_capacity)[0] - used[0];
	if (aligned_grow > unused) {
		// Not enough space
		slice_clear(result);
		return;
	}
	used[0] += aligned_grow;
	slice_assign_comp(result, old_ptr, aligned_grow + requested_size);
	mem_zero(old_ptr + old_len, grow_amount * cast(U8, should_zero));
}
S_ inline void farena__shrink__u(U8 result, U8 arena, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment) {
	assert(result != null);
	assert(arena  != null);
	U8_R used = u8_r(arena + FArena_used);
	/*Check if the allocation is at the end of the arena*/ {
		U8 alloc_end = old_ptr + old_len;
		U8 arena_end = u8_r(arena + FArena_start)[0] + used[0];
		if (alloc_end != arena_end) {
			// Not at the end, can't shrink but return adjusted size
			slice_assign_comp(result, old_ptr, requested_size);
			return;
		}
	}
	U8 aligned_original = align_pow2(old_len, MEMORY_ALIGNMENT_DEFAULT);
	U8 aligned_new      = align_pow2(requested_size, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	used[0] -= (aligned_original - aligned_new);
	slice_assign_comp(result, old_ptr, requested_size);
}
I_ void farena_reset__u(U8 arena) { u8_r(arena + FArena_used)[0] = 0; }
I_ void farena_rewind__u(U8 arena, U8 sp_slot) {
	U8   start = u8_r(arena + FArena_start)[0];
	U8_R used  = u8_r(arena + FArena_used);
	U8   end   = start + used[0]; assert_bounds(sp_slot, start, end);
	used[0] -= sp_slot - start;
}
I_ void farena_save__u(U8 arena, U8 sp) {
	u8_r(sp + AllocatorSP_type_sig)[0] = (U8)& farena_allocator_proc;
	u8_r(sp + AllocatorSP_slot    )[0] = u8_r(arena + FArena_used)[0];
}
S_ void farena_allocator_proc(U8 arena, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, /*AllocatorProc_Out*/U8 out)
{
	assert(out   != null);
	assert(arena != null);
	U8 allocation = arena + AllocatorProc_Out_allocation;
	switch (op)
	{
	case AllocatorOp_Alloc:
	case AllocatorOp_Alloc_NoZero:
		farena__push__u(arena, requested_size, 1, alignment, allocation);
		mem_zero(u8_r(allocation + Slice_ptr)[0], u8_r(allocation + Slice_len)[0] * op);
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

	case AllocatorOp_Rewind:    farena_rewind__u(arena, old_len); break;
	case AllocatorOp_SavePoint: farena_save__u(arena, allocation);         break;

	case AllocatorOp_Query:
		u4_r(out + AllocatorQueryInfo_features)[0] =
			AllocatorQuery_Alloc
		| AllocatorQuery_Reset
		| AllocatorQuery_Resize
		| AllocatorQuery_Rewind
		;
		U8 max_alloc = u8_r(arena + FArena_capacity)[0] - u8_r(arena + FArena_used)[0];
		u8_r(out + AllocatorQueryInfo_max_alloc)[0] = max_alloc;
		u8_r(out + AllocatorQueryInfo_min_alloc)[0] = 0;
		u8_r(out + AllocatorQueryInfo_left     )[0] = max_alloc;
		farena_save__u(arena, out + AllocatorQueryInfo_save_point);
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
#define MS_INVALID_HANDLE_VALUE    ((MS_HANDLE)(S8)-1)
#define MS_ANYSIZE_ARRAY           1
#define MS_MEM_COMMIT              0x00001000
#define MS_MEM_RESERVE             0x00002000
#define MS_MEM_RELEASE             0x00002000
#define MS_MEM_LARGE_PAGES         0x20000000
#define MS_PAGE_READWRITE          0x04
#define MS_TOKEN_ADJUST_PRIVILEGES (0x0020)
#define MS_SE_PRIVILEGE_ENABLED    (0x00000002L)
#define MS_TOKEN_QUERY             (0x0008)
#define MS__TEXT(quote)            L ## quote
#define MS_TEXT(quote)             MS__TEXT(quote)
#define MS_SE_LOCK_MEMORY_NAME     MS_TEXT("SeLockMemoryPrivilege")

typedef U4 MS_BOOL;
typedef U4 MS_DWORD;
typedef U8 MS_PDWORD;
typedef U8 MS_HANDLE;
typedef U8 MS_PHANDLE;
typedef U4 MS_LONG;
typedef U8 MS_LONGLONG;
typedef U8 MS_LPCSTR;
typedef U8 MS_LPWSTR, MS_PWSTR;
typedef U8 MS_LPVOID;
typedef U8 MS_LPDWORD;
typedef U8 MS_ULONG_PTR, MS_PULONG_PTR;
typedef U8 MS_LPCVOID;
typedef struct MS_SECURITY_ATTRIBUTES MS_SECURITY_ATTRIBUTES; typedef U8 MS_PSECURITY_ATTRIBUTES, MS_LPSECURITY_ATTRIBUTES;
typedef struct MS_OVERLAPPED          MS_OVERLAPPED;          typedef U8 MS_LPOVERLAPPED;
typedef def_union(MS_LARGE_INTEGER)        { struct { MS_DWORD LowPart; MS_LONG HighPart; } _; struct { MS_DWORD LowPart; MS_LONG HighPart; } u; MS_LONGLONG QuadPart; };
typedef def_struct(MS_FILE)                { U8 _Placeholder; };
typedef def_struct(MS_SECURITY_ATTRIBUTES) { MS_DWORD  nLength; A4_B1 _PAD_; MS_LPVOID lpSecurityDescriptor; MS_BOOL bInheritHandle; };
typedef def_struct(MS_OVERLAPPED)          { MS_ULONG_PTR Internal; MS_ULONG_PTR InternalHigh; union { struct { MS_DWORD Offset; MS_DWORD OffsetHigh; } _; U8 Pointer; } _; MS_HANDLE  hEvent; };
typedef struct MS_LUID                MS_LUID;                typedef U8 MS_PLUID;
typedef struct MS_LUID_AND_ATTRIBUTES MS_LUID_AND_ATTRIBUTES; typedef U8 MS_PLUID_AND_ATTRIBUTES;
typedef struct MS_TOKEN_PRIVILEGES    MS_TOKEN_PRIVILEGES;    typedef U8 MS_PTOKEN_PRIVILEGES;
typedef def_struct(MS_LUID)                { MS_DWORD LowPart;        MS_LONG HighPart; };
typedef def_struct(MS_LUID_AND_ATTRIBUTES) { MS_LUID  Luid;           MS_DWORD Attributes; };
typedef def_struct(MS_TOKEN_PRIVILEGES)    { MS_DWORD PrivilegeCount; MS_LUID_AND_ATTRIBUTES Privileges[MS_ANYSIZE_ARRAY]; };

W_ MS_BOOL   ms_close_handle(MS_HANDLE hObject) __asm__("CloseHandle");
W_ MS_BOOL   ms_adjust_token_privleges(MS_HANDLE TokenHandle, MS_BOOL DisableAllPrivileges, MS_PTOKEN_PRIVILEGES NewState, MS_DWORD BufferLength, MS_PTOKEN_PRIVILEGES PreviousState, MS_PDWORD ReturnLength) __asm__("AdjustTokenPrivileges");
W_ MS_HANDLE ms_get_current_process(void) __asm__("GetCurrentProcess");
W_ U8        ms_get_larg_page_minimum(void) __asm__("GetLargePageMinimum");
W_ MS_BOOL   ms_lookup_priviledge_value_w(MS_LPWSTR lpSystemName, MS_LPWSTR lpName, MS_PLUID lpLuid) __asm__("LookupPrivilegeValueW");
W_ MS_BOOL   ms_open_process_token(MS_HANDLE ProcessHandle, MS_DWORD DesiredAccess, MS_PHANDLE TokenHandle) __asm__("OpenProcessToken");
W_ MS_LPVOID ms_virtual_alloc(MS_LPVOID lpAddress, U8 dwSize, MS_DWORD flAllocationType, MS_DWORD flProtect) __asm__("VirtualAlloc");
W_ MS_BOOL   ms_virtual_free(MS_LPVOID lpAddress, U8 dwSize, MS_DWORD dwFreeType) __asm__("VirtualFree");
#pragma warning(pop)

I_ U8 os_system_info(void) {
	return u8_(& os__windows_info.system_info);
}
I_ void os__enable_large_pages(void) {
	MS_HANDLE token;
	if (ms_open_process_token(ms_get_current_process(), MS_TOKEN_ADJUST_PRIVILEGES | MS_TOKEN_QUERY, u8_(& token))) {
		MS_LUID luid;
		if (ms_lookup_priviledge_value_w(0, u8_(MS_SE_LOCK_MEMORY_NAME), u8_(& luid))) {
			MS_TOKEN_PRIVILEGES priv;
			priv.PrivilegeCount           = 1;
			priv.Privileges[0].Luid       = luid;
			priv.Privileges[0].Attributes = MS_SE_PRIVILEGE_ENABLED;
			ms_adjust_token_privleges(token, 0, u8_(& priv), size_of(priv), 0, 0);
		}
		ms_close_handle(token);
	}
}
S_ inline 
void os_init(void) {
	// os__enable_large_pages();
	u8_r(os_system_info() + OS_SystemInfo_target_page_size)[0] = ms_get_larg_page_minimum();
}
I_ U8 os_vmem_reserve__u(U8 size, B4 no_large_pages, U8 base_addr) {
	return cast(U8, ms_virtual_alloc(cast(MS_LPVOID, base_addr), size, MS_MEM_RESERVE,
		MS_PAGE_READWRITE /* | (opts->no_large_pages ? 0 : MS_MEM_LARGE_PAGES) */)
	);
}
I_ B4   os_vmem_commit__u (U8 vm, U8 size, B4 no_large_pages) { 
	// if (no_large_pages == false ) { return 1; }
	return ms_virtual_alloc(cast(MS_LPVOID, vm), size, MS_MEM_COMMIT, MS_PAGE_READWRITE) != null; 
}
I_ void os_vmem_release__u(U8 vm, U8 size) { ms_virtual_free(cast(MS_LPVOID, vm), 0, MS_MEM_RELEASE); }

I_ U8   os__vmem_reserve( U8 size, Opts_vmem_R opts) { 
	assert(opts != nullptr);
	return os_vmem_reserve__u(size, opts->no_large_pages, opts->base_addr); 
}
I_ B4 os__vmem_commit (U8 vm, U8 size, Opts_vmem_R opts) { 
	assert(opts != nullptr);
	return os_vmem_commit__u(vm, size, opts->no_large_pages); 
}
I_ void os_vmem_release(U8 vm, U8 size) { os_vmem_release__u(vm, size); }
#pragma endregion OS

#pragma region VArena (Virtual Address Space Arena)
I_ U8 varena_header_size(void) { return align_pow2(size_of(VArena), MEMORY_ALIGNMENT_DEFAULT); }

S_ inline U8 varena__make__u(U8 reserve_size, U8 commit_size, U4 flags, U8 base_addr) {
	if (reserve_size == 0) { reserve_size = mega(64); }
	if (commit_size  == 0) { commit_size  = mega(64); }
	U8 page       = u8_r(os_system_info() + OS_SystemInfo_target_page_size)[0];
	U8 reserve_sz = align_pow2(reserve_size, page);
	U8 commit_sz  = align_pow2(commit_size,  page);
	B4 no_large   = (flags & VArenaFlag_NoLargePages) != 0;
	U8 base       = os_vmem_reserve__u(reserve_sz, no_large, base_addr); assert(base != 0);
	B4 ok         = os_vmem_commit__u(base, commit_sz, no_large);	       assert(ok   != 0);
	U8 header     = varena_header_size();
	U8 data_start = base + header;
	u8_r(base + VArena_reserve_start)[0] = base;
	u8_r(base + VArena_reserve      )[0] = reserve_sz;
	u8_r(base + VArena_commit_size  )[0] = commit_sz;
	u8_r(base + VArena_committed    )[0] = commit_sz;
	u8_r(base + VArena_commit_used  )[0] = header;
	u4_r(base + VArena_flags        )[0] = flags;
	return base;
}
S_ inline void varena__push__u(U8 vm, U8 amount, U8 type_width, U8 alignment, U8 result) {
	assert(result != null);
	assert(vm  != null);
	if (amount == 0) { slice_clear(result); return; }
	alignment = alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT;
	U8   requested_size = amount * type_width;
	U8   aligned_size   = align_pow2(requested_size, alignment);
	U8_R commit_used    = u8_r(vm + VArena_commit_used);
	U8   to_be_used     = commit_used[0] + aligned_size;
	U8   reserve_left   = u8_r(vm + VArena_reserve  )[0] - commit_used[0];
	U8   committed      = u8_r(vm + VArena_committed)[0];
	U8   commit_left    = committed - commit_used[0];
	assert(to_be_used< reserve_left);
	if (/*exhausted?*/commit_left < aligned_size) {
		U8 commit_size      = u8_r(vm + VArena_commit_size)[0];
		U8 next_commit_size = reserve_left > aligned_size ? max(commit_size, aligned_size) : reserve_left;
		if (next_commit_size != 0) {
			B4 no_large_pages = (u4_r(vm + VArena_flags)[0] & VArenaFlag_NoLargePages) != 0;
			U8 next_commit_start = vm + committed;
			if (os_vmem_commit__u(next_commit_start, next_commit_size, no_large_pages) == false) {
				slice_clear(result);
				return;
			}
			committed += next_commit_size;
			u8_r(vm + VArena_committed)[0] = committed;
		}
	}
	commit_used[0] += aligned_size;
	U8 current_offset = u8_r(vm + VArena_reserve_start)[0] + commit_used[0];
	slice_assign_comp(result, current_offset, requested_size);
}
S_ inline void varena__grow__u(U8 result, U8 vm, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment, B4 should_zero) {
	assert(vm     != null);
	assert(result != null);
	U8 grow_amount = requested_size - old_len;
	if (grow_amount == 0) { slice_assign_comp(result, old_ptr, old_len); return; }
	U8 current_offset = u8_r(vm + VArena_reserve_start)[0] + u8_r(vm + VArena_commit_used)[0];
	// Growing when not the last allocation not allowed
	assert(old_ptr == current_offset); 
	uvar(Slice_Mem, allocation); varena__push__u(vm, grow_amount, 1, alignment, u8_(allocation));
	U8 a_ptr = u8_r(allocation + Slice_ptr)[0];
	U8 a_len = u8_r(allocation + Slice_len)[0];
	assert(a_ptr != 0);
	mem_zero(a_ptr, a_len * should_zero);
	slice_assign_comp(result, old_ptr, old_len + a_len);
}
S_ inline void varena__shrink__u(U8 result, U8 vm, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment) {
	assert(vm     != null);
	assert(result != null);
	U8 shrink_amount = old_len - requested_size;
	if (lt_s(shrink_amount, 0)) { slice_assign_comp(result, old_ptr, old_len); return; }
	U8_R commit_used    = u8_r(vm + VArena_commit_used);
	U8   current_offset = u8_r(vm + VArena_reserve_start)[0] + commit_used[0]; assert(old_ptr == current_offset);
	commit_used[0]   -= shrink_amount;
	slice_assign_comp(result, old_ptr, requested_size);
}
I_ void varena_release__u(U8 vm) {
	assert(vm != null);
	os_vmem_release__u(vm, u8_r(vm + VArena_reserve)[0]);
}
I_ void varena_reset__u(U8 vm) {
	assert(vm != null);
	u8_r(vm + VArena_commit_used)[0] = 0;
}
I_ void varena_rewind__u(U8 vm, U8 sp_slot) {
	assert(vm       != null);
	U8 header = varena_header_size();
	if (sp_slot < header) { sp_slot = header; }
	u8_r(vm + VArena_commit_used)[0] = sp_slot;
}
I_ void varena_save__u(U8 vm, U8 sp_addr) {
	assert(vm   != null);
	assert(sp_addr != null);
	u8_r(sp_addr + AllocatorSP_type_sig)[0] = (U8) varena_allocator_proc;
	u8_r(sp_addr + AllocatorSP_slot    )[0] = u8_r(vm + VArena_commit_used)[0];
}

I_ VArena* varena__make(Opts_varena_make*R_ opts) {
	assert(opts != nullptr);
	return cast(VArena*, varena__make__u(opts->reserve_size, opts->commit_size, opts->flags, opts->base_addr));
}
I_ Slice_Mem varena__push(VArena_R vm, U8 amount, U8 type_width, Opts_varena* opts) {
	Slice_Mem result;
	varena__push__u(u8_(vm), amount, type_width, opts ? opts->alignment : 0, u8_(& result));
	return result;
}
I_ Slice_Mem varena__shrink(VArena_R vm, Slice_Mem old_allocation, U8 requested_size, Opts_varena* opts) {
	Slice_Mem result;
	varena__shrink__u(u8_(& result), u8_(vm), old_allocation.ptr, old_allocation.len, requested_size, opts ? opts->alignment : 0);
	return result;
}

I_ void varena_release(VArena_R vm) { varena_release__u(u8_(vm)); }
I_ void varena_reset  (VArena_R vm) { varena_reset__u  (u8_(vm)); }

I_ void varena_rewind (VArena_R vm, AllocatorSP save_point) { 
	assert(save_point.type_sig == varena_allocator_proc);
	varena_rewind__u(u8_(vm), save_point.slot);
}
I_ AllocatorSP varena_save(VArena_R vm) { AllocatorSP sp; varena_save__u(u8_(vm), u8_(& sp)); return sp; }
S_ void varena_allocator_proc(U8 vm, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, U8 out_addr)
{
	assert(vm       != null);
	assert(out_addr != null);
	U8 out_allocation = out_addr ? out_addr + AllocatorProc_Out_allocation : 0;
	switch (op)
	{
	case AllocatorOp_Alloc:
	case AllocatorOp_Alloc_NoZero:
		varena__push__u(vm, requested_size, 1, alignment, out_allocation);
		if (op == AllocatorOp_Alloc) {
			U8 ptr = u8_r(out_allocation + Slice_ptr)[0];
			U8 len = u8_r(out_allocation + Slice_len)[0];
			if (ptr && len) { mem_zero(ptr, len); }
		}
	break;

	case AllocatorOp_Free:                          break;
	case AllocatorOp_Reset: varena_reset__u(vm); break;

	case AllocatorOp_Grow:
	case AllocatorOp_Grow_NoZero:
		varena__grow__u(out_allocation, vm, old_ptr, old_len, requested_size, alignment, op - AllocatorOp_Grow_NoZero);
	break;
	case AllocatorOp_Shrink:
		varena__shrink__u(out_allocation, vm, old_ptr, old_len, requested_size, alignment);
	break;

	case AllocatorOp_Rewind:    varena_rewind__u(vm, old_len);                                 break;
	case AllocatorOp_SavePoint: varena_save__u  (vm, out_addr + AllocatorProc_Out_save_point); break;

	case AllocatorOp_Query:
			u4_r(out_addr + AllocatorQueryInfo_features)[0] =
			  AllocatorQuery_Alloc
			| AllocatorQuery_Reset
			| AllocatorQuery_Resize
			| AllocatorQuery_Rewind;
			U8 reserve   = u8_r(vm + VArena_reserve  )[0];
			U8 committed = u8_r(vm + VArena_committed)[0];
			U8 max_alloc = (reserve > committed) ? (reserve - committed) : 0;
			u8_r(out_addr + AllocatorQueryInfo_max_alloc)[0] = max_alloc;
			u8_r(out_addr + AllocatorQueryInfo_min_alloc)[0] = kilo(4);
			u8_r(out_addr + AllocatorQueryInfo_left     )[0] = max_alloc;
			AllocatorSP sp = { .type_sig = varena_allocator_proc, .slot = u8_r(vm + VArena_commit_used)[0] };
			struct_assign(AllocatorSP, out_addr + AllocatorQueryInfo_save_point, (U8)& sp);
	break;
	}
}
#pragma endregion VArena

#pragma region Arena
I_ U8 arena_header_size(void) { return align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT); }

S_ inline U8 arena_make__u(U8 reserve_size, U8 commit_size, U4 flags, U8 base_addr) {
	U8 header_size = arena_header_size();
	U8 current     = varena__make__u(reserve_size, commit_size, flags, base_addr); assert(current != null);
	U8 arena; varena__push__u(current, header_size, 1, MEMORY_ALIGNMENT_DEFAULT, (U8)& arena);
	u8_r(arena + Arena_backing )[0] = current;
	u8_r(arena + Arena_prev    )[0] = null;
	u8_r(arena + Arena_current )[0] = arena;
	u8_r(arena + Arena_base_pos)[0] = 0;
	u8_r(arena + Arena_pos     )[0] = header_size;
	u8_r(arena + Arena_flags   )[0] = flags;
	return arena;
}
S_ inline void arena__push__u(U8 arena, U8 amount, U8 type_width, U8 alignment, U8 out_mem) {
	assert(arena != null);
	U8 active          = u8_r(arena + Arena_current)[0];
	U8 size_requested  = amount * type_width;
	   alignment       = alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT;
	U8 size_aligned    = align_pow2(size_requested, alignment);
	U8 pos_pre         = u8_r(active + Arena_pos)[0];
	U8 pos_pst         = pos_pre + size_aligned;
	U8 backing         = active + Arena_backing;
	U8 reserve         = u8_r(backing + VArena_reserve)[0];
	B4 should_chain    = 
     ((u8_r(arena + Arena_flags)[0] & ArenaFlag_NoChain) == 0)
	&& reserve < pos_pst;
	if (should_chain)
	{
		U8 current   = arena + Arena_current;
		U8 new_arena = arena_make__u(
			reserve, 
			u8_r(backing + VArena_commit_size)[0], 
			u4_r(backing + VArena_flags      )[0], 
			0
		);
		u8_r(new_arena + Arena_base_pos)[0] = u8_r(active + Arena_base_pos)[0] + reserve;
		u8_r(new_arena + Arena_prev    )[0] = u8_r(current)[0];
		u8_r(current)[0]                    = new_arena;
		active                              = u8_r(current)[0];
	}
	U8 result = active + pos_pre;
	varena__push__u(u8_r(backing)[0], size_aligned, 1, alignment, out_mem);
	assert(u8_r(out_mem + Slice_ptr)[0] == result);
	assert(u8_r(out_mem + Slice_len)[0] >  0);
	u8_r(active + Arena_pos)[0] = pos_pst;
}
S_ inline void arena__grow__u(U8 arena, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment, B4 should_zero, U8 out_mem) {
	U8   active     = arena + Arena_current;
	U8_R active_pos = u8_r(active + Arena_pos);
	U8   alloc_end  = old_ptr + old_len;
	U8   arena_end  = active + active_pos[0];
	if (alloc_end == arena_end)
	{
		U8 grow_amount  = requested_size - old_len;
		U8 aligned_grow = align_pow2(grow_amount, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
		if (active_pos[0] + aligned_grow <= u8_r(active + Arena_backing + VArena_reserve)[0]) {
			uvar(Slice_Mem, vresult); varena__push__u(u8_r(active + Arena_backing)[0], aligned_grow, 1, alignment, (U8)vresult);
			if (u8_r(vresult + Slice_ptr)[0] != null) {
				active_pos[0] += aligned_grow;
				mem_zero(old_ptr + old_len, aligned_grow * should_zero);
				slice_assign_comp(out_mem, u8_(vresult) + Slice_ptr, u8_(vresult) + Slice_len);
				return;
			}
		}
	}
	arena__push__u(arena, requested_size, 1, alignment, out_mem);
	if (u8_r(out_mem + Slice_ptr)[0] == null) { slice_assign_comp(out_mem, 0, 0); return; }
	mem_copy(u8_r(out_mem + Slice_ptr)[0], old_ptr, old_len);
	mem_zero(u8_r(out_mem + Slice_ptr)[0], (u8_r(out_mem + Slice_len)[0] - old_len) * should_zero);
}
S_ inline void arena__shrink__u(U8 arena, U8 old_ptr, U8 old_len, U8 requested_size, U8 alignment, U8 out_mem) {
	U8   active     = arena + Arena_current;
	U8_R active_pos = u8_r(active + Arena_pos);
	U8   alloc_end  = old_ptr + old_len;
	U8   arena_end  = active + active_pos[0];
	if (alloc_end != arena_end) { slice_assign_comp(out_mem, old_ptr, old_len); return; }
	U8 aligned_original = align_pow2(old_len, MEMORY_ALIGNMENT_DEFAULT);
	U8 aligned_new      = align_pow2(requested_size, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8 pos_reduction    = aligned_original - aligned_new;
	u8_r(active + Arena_pos)[0] -= pos_reduction;
	varena__shrink__u(out_mem, active + Arena_backing, old_ptr, old_len, requested_size, alignment);
}
I_ void arena_release__u(U8 arena) {
	assert(arena != null);
	U8 curr = arena + Arena_current; 
	U8 prev = null;
	for (; u8_r(curr)[0] != null; curr = prev) {
		u8_r(prev)[0] = u8_r(curr + Arena_prev)[0];
		varena_release__u(u8_r(curr)[0]);
	}
}
I_ void arena_reset__u(U8 arena) { arena_rewind__u(arena, 0); }
void arena_rewind__u(U8 arena, U8 slot) {
	assert(arena != null);
	U8 header_size = arena_header_size();
	U8 curr        = arena + Arena_current;
	U8 big_pos     = clamp_bot(header_size, slot);
	for (U8 prev = null; u8_r(curr + Arena_base_pos)[0] >= big_pos; u8_r(curr)[0] = prev) {
		prev = u8_r(curr + Arena_prev)[0];
		varena_release__u(u8_r(curr + Arena_backing)[0]);
	}
	u8_r(arena + Arena_current)[0] = u8_r(curr)[0];
	U8 new_pos = big_pos - u8_r(curr + Arena_base_pos)[0]; assert(new_pos <= u8_r(curr + Arena_pos)[0]);
	u8_r(curr + Arena_pos)[0] = new_pos;
}
I_ void arena_save__u(U8 arena, U8 out_sp) {
	u8_r(out_sp + AllocatorSP_type_sig)[0] = (U8)& arena_allocator_proc;
	u8_r(out_sp + AllocatorSP_slot    )[0] = 
	    u8_r(arena + Arena_base_pos           )[0] 
		+ u8_r(arena + Arena_current + Arena_pos)[0];
}
S_ inline void arena_allocator_proc(U8 arena, U8 requested_size, U8 alignment, U8 old_ptr, U8 old_len, U4 op, U8 out_addr)
{
	assert(out_addr != null);
	assert(arena    != null);
	U8 out_allocation = out_addr + AllocatorProc_Out_allocation;
	switch (op)
	{
	case AllocatorOp_Alloc:
	case AllocatorOp_Alloc_NoZero:
		arena__push__u(arena, requested_size, 1, alignment, out_allocation);
		mem_zero(out_allocation, u8_r(out_allocation + Slice_len)[0] * op);
	break;

	case AllocatorOp_Free:                         break;
	case AllocatorOp_Reset: arena_reset__u(arena); break;

	case AllocatorOp_Grow:
	case AllocatorOp_Grow_NoZero:
		arena__grow__u(arena, old_ptr, old_len, requested_size, alignment, op - AllocatorOp_Grow_NoZero, out_allocation);
	break;
	case AllocatorOp_Shrink:
		arena__shrink__u(arena, old_ptr, old_len, requested_size, alignment, out_allocation);
	break;

	case AllocatorOp_Rewind:    arena_rewind__u(arena, old_len);                               break;
	case AllocatorOp_SavePoint: arena_save__u(arena, out_addr + AllocatorProc_Out_save_point); break;

	case AllocatorOp_Query:
		u4_r(out_addr + AllocatorQueryInfo_features)[0] = 
			AllocatorQuery_Alloc
		|	AllocatorQuery_Resize
		|	AllocatorQuery_Reset
		|	AllocatorQuery_Rewind
		;
		u8_r(out_addr + AllocatorQueryInfo_max_alloc )[0] = u8_r(arena + Arena_backing + VArena_reserve)[0];
		u8_r(out_addr + AllocatorQueryInfo_min_alloc )[0] = kilo(4);
		u8_r(out_addr + AllocatorQueryInfo_left      )[0] = u8_r(out_addr + AllocatorQueryInfo_max_alloc)[0] - u8_r(arena + Arena_backing + VArena_commit_used)[0];
		arena_save__u(arena, out_addr + AllocatorQueryInfo_save_point);
	break;
	}
}

I_ Arena* arena__make(Opts_arena_make*R_ opts) {
	assert(opts != nullptr);
	return cast(Arena*, arena_make__u(opts->reserve_size, opts->commit_size, opts->flags, opts->base_addr));
}
#pragma endregion Arena

#pragma region Key Table Linear (KTL)
I_ void ktl_populate_slice_a2_str8(U8 kt, U8 backing_ptr, U8 backing_len, U8 values) {
	assert(kt != null);
	U8 values_len = u8_r(values + Slice_len)[0];
	if (values_len == 0) return;
	mem__alloc__u(kt, backing_ptr, backing_len, size_of(KTL_Slot_Str8) * values_len, 0, false);
	for (U8 id = 0; id < values_len; ++id) { 
		U8 kt_slot = kt + Slice_ptr * id; 
		U8 value   = u8_r(values + Slice_ptr + size_of(A2_Str8) * id)[0];
		mem_copy        (kt_slot + KTL_Slot_value, value + size_of(Str8) * 1, size_of(Str8));
		hash64__fnv1a__u(kt_slot + KTL_Slot_key,   value);
	}
}
#pragma endregion KTL

#pragma region Key Table 1-Layer Chained-Chunked_Cells (KT1CX)
S_ inline void kt1cx_init__u(U8 backing_tbl, U8 backing_cells, U8 m, U8 result) {
	assert(result != null);
	assert(u8_r(backing_cells + AllocatorInfo_proc)[0] != null);
	assert(u8_r(backing_tbl   + AllocatorInfo_proc)[0] != null);
	U8 table_size = u8_r(m + KT1CX_InfoMeta_table_size)[0];
	assert(u8_r(m + KT1CX_InfoMeta_cell_depth    )[0] > 0);
	assert(u8_r(m + KT1CX_InfoMeta_cell_pool_size)[0] >= kilo(4));
	assert(table_size                                 >= kilo(4));
	assert(u8_r(m + KT1CX_InfoMeta_type_width    )[0] >= 0);
	U8 alloc_size = table_size + u8_r(m + KT1CX_InfoMeta_cell_size)[0];
	mem__alloc__u(result, backing_tbl, backing_tbl + AllocatorInfo_data, alloc_size, 0, 0); 
	assert(u8_r(result + Slice_ptr)[0] != null);
	assert(u8_r(result + Slice_len)[0] >  0);
	u8_r(result + Slice_len)[0] = table_size;
}
S_ inline void kt1cx_clear__u(U8 kt, U8 m) {
	U8 cell_cursor = u8_r(kt + Slice_ptr)[0];
	U8 cell_size   = u8_r(m  + KT1CX_ByteMeta_cell_size)[0];
	U8 cell_depth  = u8_r(m  + KT1CX_ByteMeta_cell_depth)[0];
	U8 table_len   = u8_r(kt + Slice_len)[0] * cell_size;
	U8 table_end   = cell_cursor + table_len;
	U8 slot_size   = u8_r(m + KT1CX_ByteMeta_slot_size)[0];
	for (; cell_cursor != table_end; cell_cursor += cell_size)
	{
		U8 slots_end   = cell_cursor + (cell_depth * slot_size); 
		U8 slot_cursor = cell_cursor;
		for (; slot_cursor < slots_end; slot_cursor += slot_size) {
		process_slots:
			mem_zero(slot_cursor, slot_size);
		}
		U8 next = slot_cursor + u8_r(m + KT1CX_ByteMeta_cell_next_offset)[0];
		if (next != null) {
			slot_cursor = next;
			slots_end   = slot_cursor + (cell_depth * slot_size);
			goto process_slots;
		}
	}
}
I_ U8 kt1cx_slot_id__u(U8 kt, U8 key) {
	return key % u8_r(kt + Slice_len)[0];
}
S_ inline U8 kt1cx_get__u(U8 kt, U8 key, U8 m) {
	U8 hash_index  = kt1cx_slot_id__u(kt, key);
	U8 cell_offset = hash_index * u8_r(m + KT1CX_ByteMeta_cell_size)[0];
	U8 cell_cursor = u8_r(kt + Slice_ptr)[0] + cell_offset;
	{
		U8 slot_size   = u8_r(m + KT1CX_ByteMeta_slot_size)[0];
		U8 slot_cursor = cell_cursor;
		U8 slots_end   = cell_cursor + u8_r(m + KT1CX_ByteMeta_cell_depth)[0] * slot_size;
		for (; slot_cursor != slots_end; slot_cursor += slot_size) {
		process_slots:
			if (u8_r(slot_cursor + KT1CX_Byte_Slot_occupied)[0] && u8_r(slot_cursor + KT1CX_Byte_Slot_key)[0] == key) {
				return slot_cursor;
			}
		}
		U8 cell_next = cell_cursor + u8_r(m + KT1CX_ByteMeta_cell_next_offset)[0];
		if (cell_next != null) {
			slot_cursor = cell_next;
			cell_cursor = cell_next;
			goto process_slots;
		}
		else {
			return null;
		}
	}
}
S_ inline U8 kt1cx_set__u(U8 kt, U8 key, U8 v_ptr, U8 v_len, U8 backing_cells, U8 m) {
	(void)v_ptr;
	(void)v_len;
	assert(kt != null);
	assert(m  != null);
	U8 table_len = u8_r(kt + Slice_len)[0];
	U8 table_ptr = u8_r(kt + Slice_ptr)[0];
	if (table_len == 0 || table_ptr == 0) { return null; }

	U8 cell_size        = u8_r(m + KT1CX_ByteMeta_cell_size)[0];
	U8 cell_depth       = u8_r(m + KT1CX_ByteMeta_cell_depth)[0];
	U8 slot_size        = u8_r(m + KT1CX_ByteMeta_slot_size)[0];
	U8 slot_key_offset  = u8_r(m + KT1CX_ByteMeta_slot_key_offset)[0];
	U8 cell_next_offset = u8_r(m + KT1CX_ByteMeta_cell_next_offset)[0];
	U8 slot_span        = cell_depth * slot_size;

	U8 hash_index  = key % table_len;
	U8 cell_cursor = table_ptr + hash_index * cell_size;

process_cell:
	{
		U8 slot_cursor = cell_cursor;
		U8 slots_end   = cell_cursor + slot_span;
		for (; slot_cursor != slots_end; slot_cursor += slot_size) {
		process_slots:
			U8 slot_key_addr = slot_cursor + slot_key_offset;
			U8 slot_occ_addr = slot_cursor + KT1CX_Byte_Slot_occupied;
			if (!u8_r(slot_occ_addr)[0]) {
				u8_r(slot_occ_addr)[0] = 1;
				u8_r(slot_key_addr)[0] = key;
				return slot_cursor;
			}
			if (u8_r(slot_key_addr)[0] == key) {
				return slot_cursor;
			}
		}

		U8 next_addr = cell_cursor + cell_next_offset;
		U8 next_cell = u8_r(next_addr)[0];
		if (next_cell != null) {
			slot_cursor = next_cell;
			cell_cursor = next_cell;
			goto process_slots;
		}

		uvar(Slice_Mem, new_cell);
		mem__alloc__u(
			u8_(new_cell),
			u8_r(backing_cells + AllocatorInfo_proc)[0],
			u8_r(backing_cells + AllocatorInfo_data)[0],
			cell_size,
			0,
			false);
		U8 new_cell_ptr = u8_r(new_cell + Slice_ptr)[0];
		if (new_cell_ptr == 0) { return null; }
		mem_zero(new_cell_ptr, cell_size);

		u8_r(next_addr)[0] = new_cell_ptr;
		cell_cursor        = new_cell_ptr;
		goto process_cell;
	}
}

I_ void kt1cx_init(KT1CX_Info info, KT1CX_InfoMeta meta, KT1CX_Byte*R_ result) {
	assert(result != nullptr);
	kt1cx_init__u(u8_(& info.backing_table), u8_(& info.backing_cells), u8_(& meta), u8_(& result->table));
}

I_ void kt1cx_clear(KT1CX_Byte kt, KT1CX_ByteMeta meta) {
	kt1cx_clear__u(u8_(& kt.table), u8_(& meta));
}

I_ U8 kt1cx_slot_id(KT1CX_Byte kt, U8 key, KT1CX_ByteMeta meta) {
	(void)meta;
	return kt1cx_slot_id__u(u8_(& kt.table), key);
}

I_ U8 kt1cx_get(KT1CX_Byte kt, U8 key, KT1CX_ByteMeta meta) {
	return kt1cx_get__u(u8_(& kt.table), key, u8_(& meta));
}

I_ U8 kt1cx_set(KT1CX_Byte kt, U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta meta) {
	return kt1cx_set__u(u8_(& kt.table), key, value.ptr, value.len, u8_(& backing_cells), u8_(& meta));
}
#pragma endregion Key Table

#pragma region String Operations
I_ B4 char_is_upper(U1 c) { return ('A' <= c && c <= 'Z'); }
I_ U1 char_to_lower(U1 c) { if (char_is_upper(c)) { c += ('a' - 'A'); } return c; }
I_ U1 integer_symbols(U1 value) {
	LP_ U1 lookup_table[16] = { '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F' };
	return lookup_table[value & 0xF];
}

S_ U8 str8_to_cstr_capped__u(U8 str_slice, U8 mem_slice) {
	assert(str_slice != null);
	assert(mem_slice != null);
	U8 src_ptr = u8_r(str_slice + Str8_ptr)[0];
	U8 src_len = u8_r(str_slice + Str8_len)[0];
	U8 dst_ptr = u8_r(mem_slice + Slice_ptr)[0];
	U8 dst_len = u8_r(mem_slice + Slice_len)[0];
	assert(dst_ptr != null);
	assert(dst_len > 0);
	U8 max_copy = dst_len - 1;
	U8 copy_len = min(src_len, max_copy);
	mem_copy(dst_ptr, src_ptr, copy_len);
	u1_r(dst_ptr)[copy_len] = 0;
	return dst_ptr;
}

I_ char* str8_to_cstr_capped(Str8 content, Slice_Mem mem) {
	return cast(char*, str8_to_cstr_capped__u(u8_(& content), u8_(& mem)));
}

S_ void str8_from_u32__u(U8 result, U8 ainfo_proc, U8 ainfo_data, U4 num, U4 radix, U4 min_digits, U4 digit_group_separator) {
	assert(result     != null);
	assert(ainfo_proc != null);
	U8 prefix_ptr = 0;
	U8 prefix_len = 0;
	switch (radix) {
	case 16: { Str8 temp = lit("0x"); prefix_ptr = temp.ptr; prefix_len = temp.len; } break;
	case 8:  { Str8 temp = lit("0o"); prefix_ptr = temp.ptr; prefix_len = temp.len; } break;
	case 2:  { Str8 temp = lit("0b"); prefix_ptr = temp.ptr; prefix_len = temp.len; } break;
	default: break;
	}
	U4 digit_group_size = (radix == 2 || radix == 8 || radix == 16) ? 4 : 3;
	U4 needed_digits = 1;
	for (U4 reduce = num; reduce /= radix; ) { ++ needed_digits; }
	U4 needed_leading_zeros = (min_digits > needed_digits) ? min_digits - needed_digits : 0;
	U4 needed_separators = 0;
	if (digit_group_separator != 0) {
		U4 digit_total = needed_digits + needed_leading_zeros;
		needed_separators = digit_total / digit_group_size;
		if (needed_separators && (digit_total % digit_group_size) == 0) {
			-- needed_separators;
		}
	}
	U8 total_len = prefix_len + needed_leading_zeros + needed_separators + needed_digits;
	uvar(Slice_Mem, allocation);
	mem__alloc__u(u8_(allocation), ainfo_proc, ainfo_data, total_len, 0, 1);
	U8 out_ptr = u8_r(u8_(allocation) + Slice_ptr)[0];
	assert(out_ptr != null);
	u8_r(result + Str8_ptr)[0] = out_ptr;
	u8_r(result + Str8_len)[0] = total_len;

	U8 digits_until_separator = digit_group_size;
	U4 num_reduce = num;
	for (U4 idx = 0; idx < needed_digits; ++idx) {
		U8 write_pos = out_ptr + total_len - idx - 1;
		if (digit_group_separator && digits_until_separator == 0) {
			u1_r(write_pos)[0] = cast(U1, digit_group_separator);
			digits_until_separator = digit_group_size;
			++ write_pos;
		} else {
			u1_r(write_pos)[0] = char_to_lower(integer_symbols(cast(U1, num_reduce % radix)));
			num_reduce /= radix;
			if (num_reduce == 0) { break; }
		}
		if (digits_until_separator) { -- digits_until_separator; }
	}
	for (U4 leading = 0; leading < needed_leading_zeros; ++leading) {
		u1_r(out_ptr + prefix_len + leading)[0] = '0';
	}
	if (prefix_len) {
		mem_copy(out_ptr, prefix_ptr, prefix_len);
	}
}

I_ Str8 str8_from_u32(AllocatorInfo ainfo, U4 num, U4 radix, U4 min_digits, U4 digit_group_separator) {
	Str8 out = {0};
	str8_from_u32__u(u8_(& out), u8_(ainfo.proc), ainfo.data, num, radix, min_digits, digit_group_separator);
	return out;
}

S_ void str8__fmt_ktl__u(U8 result, U8 ainfo_proc, U8 ainfo_data, U8 buffer_slice, U8 table_slice, U8 fmt_slice) {
	assert(result       != null);
	assert(buffer_slice != null);
	assert(table_slice  != null);
	assert(fmt_slice    != null);

	U8 buffer_ptr = u8_r(buffer_slice + Slice_ptr)[0];
	U8 buffer_len = u8_r(buffer_slice + Slice_len)[0];
	assert(buffer_ptr != null);
	assert(buffer_len  != 0);

	U8 table_ptr = u8_r(table_slice + Slice_ptr)[0];
	U8 table_len = u8_r(table_slice + Slice_len)[0];
	assert(table_ptr != null);

	U8 fmt_ptr = u8_r(fmt_slice + Str8_ptr)[0];
	U8 fmt_len = u8_r(fmt_slice + Str8_len)[0];
	assert(fmt_ptr != null);

	if (ainfo_proc != null) {
		AllocatorQueryInfo query = {0};
		allocator_query__u(ainfo_proc, ainfo_data, u8_(& query));
		assert((query.features & AllocatorQuery_Grow) != 0);
	}

	U8 cursor_buffer    = buffer_ptr;
	U8 buffer_remaining = buffer_len;
	U8 cursor_fmt       = fmt_ptr;
	U8 fmt_end          = fmt_ptr + fmt_len;
	U8 left_fmt         = fmt_len;
	U8 slot_size        = size_of(KTL_Slot_Str8);

	while (left_fmt && buffer_remaining) {
		U8 copy_offset = 0;
		while ((cursor_fmt + copy_offset) < fmt_end && u1_r(cursor_fmt + copy_offset)[0] != '<') {
			++ copy_offset;
		}
		if (copy_offset) {
			mem_copy(cursor_buffer, cursor_fmt, copy_offset);
			buffer_remaining -= copy_offset;
			left_fmt         -= copy_offset;
			cursor_buffer    += copy_offset;
			cursor_fmt       += copy_offset;
			if (left_fmt == 0) { break; }
		}

		if ((cursor_fmt < fmt_end) && u1_r(cursor_fmt)[0] == '<') {
			U8 token_cursor = cursor_fmt + 1;
			U8 token_len    = 0;
			B4 fmt_overflow = false;
			for (;;) {
				U8 current = token_cursor + token_len;
				fmt_overflow = current >= fmt_end;
				if (fmt_overflow) { break; }
				if (u1_r(current)[0] == '>') { break; }
				++ token_len;
			}
			if (fmt_overflow) { continue; }

			U8 key = 0;
			hash64_fnv1a__u(u8_(& key), token_cursor, token_len, 0);
			U8 value_ptr = null;
			U8 value_len = 0;
			U8 slot_cursor = table_ptr;
			for (U8 slot_index = 0; slot_index < table_len; ++slot_index, slot_cursor += slot_size) {
				if (u8_r(slot_cursor + KTL_Slot_key)[0] == key) {
					U8 value_slice = slot_cursor + KTL_Slot_value;
					value_ptr = u8_r(value_slice + Str8_ptr)[0];
					value_len = u8_r(value_slice + Str8_len)[0];
					break;
				}
			}

			if (value_ptr != null) {
				if (ainfo_proc != null && (buffer_remaining - token_len) <= 0) {
					uvar(Slice_Mem, grown);
					mem__grow__u(u8_(grown), ainfo_proc, ainfo_data, buffer_ptr, buffer_len, buffer_len + token_len, 0, false, true);
					U8 grown_ptr = u8_r(u8_(grown) + Slice_ptr)[0];
					U8 grown_len = u8_r(u8_(grown) + Slice_len)[0];
					U8 used      = cursor_buffer - buffer_ptr;
					buffer_ptr   = grown_ptr;
					buffer_len   = grown_len;
					cursor_buffer    = buffer_ptr + used;
					buffer_remaining = buffer_len - used;
					u8_r(buffer_slice + Slice_ptr)[0] = buffer_ptr;
					u8_r(buffer_slice + Slice_len)[0] = buffer_len;
				}
				assert((buffer_remaining - token_len) > 0);
				mem_copy(cursor_buffer, value_ptr, value_len);
				cursor_buffer    += value_len;
				buffer_remaining -= value_len;
				cursor_fmt        = token_cursor + token_len + 1;
				left_fmt         -= token_len + 2;
				continue;
			}

			u1_r(cursor_buffer)[0] = u1_r(cursor_fmt)[0];
			++ cursor_buffer;
			++ cursor_fmt;
			-- buffer_remaining;
			-- left_fmt;
			continue;
		}
	}

	u8_r(buffer_slice + Slice_ptr)[0] = buffer_ptr;
	u8_r(buffer_slice + Slice_len)[0] = buffer_len;
	u8_r(result + Str8_ptr)[0] = buffer_ptr;
	u8_r(result + Str8_len)[0] = buffer_len - buffer_remaining;
}

I_ Str8 str8__fmt_ktl(AllocatorInfo ainfo, Slice_Mem*R_ buffer, KTL_Str8 table, Str8 fmt_template) {
	assert(buffer != nullptr);
	Str8 formatted = {0};
	str8__fmt_ktl__u(
		u8_(& formatted),
		u8_(ainfo.proc),
		ainfo.data,
		u8_(buffer),
		u8_(& table),
		u8_(& fmt_template)
	);
	return formatted;
}

S_ void str8__fmt_backed__u(U8 result, U8 tbl_backing_proc, U8 tbl_backing_data, U8 buf_backing_proc, U8 buf_backing_data, U8 fmt_slice, U8 entries_slice) {
	assert(result != null);
	KTL_Str8 kt = {0};
	ktl_populate_slice_a2_str8(u8_(& kt), tbl_backing_proc, tbl_backing_data, entries_slice);
	uvar(Slice_Mem, buffer);
	mem__alloc__u(u8_(buffer), buf_backing_proc, buf_backing_data, kilo(64), 0, 1);
	str8__fmt_ktl__u(result, buf_backing_proc, buf_backing_data, u8_(buffer), u8_(& kt), fmt_slice);
}

I_ Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8*R_ entries) {
	Str8 output = {0};
	str8__fmt_backed__u(
		u8_(& output),
		u8_(tbl_backing.proc),
		tbl_backing.data,
		u8_(buf_backing.proc),
		buf_backing.data,
		u8_(& fmt_template),
		u8_(entries)
	);
	return output;
}

S_ void str8__fmt__u(U8 result, U8 fmt_slice, U8 entries_slice) {
	assert(result != null);
	LP_ B1 tbl_mem[kilo(32)];
	LP_ B1 buf_mem[kilo(64)];
	LP_ B1 tbl_arena_mem[size_of(FArena)];
	farena_init__u(u8_(tbl_arena_mem), u8_(tbl_mem), size_of(tbl_mem));
	AllocatorInfo tbl_info = { .proc = farena_allocator_proc, .data = u8_(tbl_arena_mem) };
	KTL_Str8 kt = {0};
	ktl_populate_slice_a2_str8(u8_(& kt), u8_(tbl_info.proc), tbl_info.data, entries_slice);
	Slice_Mem buffer = slice_fmem(buf_mem);
	str8__fmt_ktl__u(result, 0, 0, u8_(& buffer), u8_(& kt), fmt_slice);
}

I_ Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8*R_ entries) {
	Str8 output = {0};
	str8__fmt__u(u8_(& output), u8_(& fmt_template), u8_(entries));
	return output;
}

S_ void str8cache__fill_byte_meta__u(U8 meta) {
	assert(meta != null);
	u8_r(meta + KT1CX_ByteMeta_slot_size)[0]        = size_of(KT1CX_Slot_Str8);
	u8_r(meta + KT1CX_ByteMeta_slot_key_offset)[0]  = offset_of(KT1CX_Slot_Str8, key);
	u8_r(meta + KT1CX_ByteMeta_cell_next_offset)[0] = offset_of(KT1CX_Cell_Str8, next);
	u8_r(meta + KT1CX_ByteMeta_cell_depth)[0]       = Str8Cache_CELL_DEPTH;
	u8_r(meta + KT1CX_ByteMeta_cell_size)[0]        = size_of(KT1CX_Cell_Str8);
	u8_r(meta + KT1CX_ByteMeta_type_width)[0]       = size_of(Str8);
	Str8 type_name = lit(stringify(Str8));
	u8_r(meta + KT1CX_ByteMeta_type_name + Str8_ptr)[0] = type_name.ptr;
	u8_r(meta + KT1CX_ByteMeta_type_name + Str8_len)[0] = type_name.len;
}

S_ void str8cache__fill_info_meta__u(U8 meta, U8 cell_pool_size, U8 table_size) {
	assert(meta != null);
	u8_r(meta + KT1CX_InfoMeta_cell_pool_size)[0] = cell_pool_size;
	u8_r(meta + KT1CX_InfoMeta_table_size)[0]     = table_size;
	u8_r(meta + KT1CX_InfoMeta_slot_size)[0]        = size_of(KT1CX_Slot_Str8);
	u8_r(meta + KT1CX_InfoMeta_slot_key_offset)[0]  = offset_of(KT1CX_Slot_Str8, key);
	u8_r(meta + KT1CX_InfoMeta_cell_next_offset)[0] = offset_of(KT1CX_Cell_Str8, next);
	u8_r(meta + KT1CX_InfoMeta_cell_depth)[0]       = Str8Cache_CELL_DEPTH;
	u8_r(meta + KT1CX_InfoMeta_cell_size)[0]        = size_of(KT1CX_Cell_Str8);
	u8_r(meta + KT1CX_InfoMeta_type_width)[0]       = size_of(Str8);
	Str8 type_name = lit(stringify(Str8));
	u8_r(meta + KT1CX_InfoMeta_type_name + Str8_ptr)[0] = type_name.ptr;
	u8_r(meta + KT1CX_InfoMeta_type_name + Str8_len)[0] = type_name.len;
}

S_ void str8cache__init__u(U8 cache, U8 opts) {
	assert(cache != null);
	assert(opts  != null);
	U8 str_reserve = cache + Str8Cache_str_reserve;
	U8 cell_reserve = cache + Str8Cache_cell_reserve;
	U8 tbl_backing  = cache + Str8Cache_tbl_backing;
	
	U8 in_str_reserve  = opts + Opts_str8cache_init_str_reserve;
	U8 in_cell_reserve = opts + Opts_str8cache_init_cell_reserve;
	U8 in_tbl_backing  = opts + Opts_str8cache_init_tbl_backing;

	assert(u8_r(in_str_reserve  + AllocatorInfo_proc)[0] != null);
	assert(u8_r(in_cell_reserve + AllocatorInfo_proc)[0] != null);
	assert(u8_r(in_tbl_backing  + AllocatorInfo_proc)[0] != null);

	mem_copy(str_reserve,  in_str_reserve,  size_of(AllocatorInfo));
	mem_copy(cell_reserve, in_cell_reserve, size_of(AllocatorInfo));
	mem_copy(tbl_backing,  in_tbl_backing,  size_of(AllocatorInfo));

	U8 cell_pool_size = u8_r(opts + Opts_str8cache_init_cell_pool_size)[0];
	U8 table_size     = u8_r(opts + Opts_str8cache_init_table_size)[0];
	if (cell_pool_size == 0) { cell_pool_size = kilo(1); }
	if (table_size     == 0) { table_size     = kilo(1); }

	uvar(KT1CX_InfoMeta, meta) = {0};
	str8cache__fill_info_meta__u(u8_(meta), cell_pool_size, table_size);
	kt1cx_init__u(tbl_backing, cell_reserve, u8_(meta), cache + Str8Cache_kt + KT1CX_Str8_table);
}

I_ void str8cache__init(Str8Cache_R cache, Opts_str8cache_init*R_ opts) {
	assert(cache != nullptr);
	assert(opts  != nullptr);
	assert(opts->str_reserve.proc  != nullptr);
	assert(opts->cell_reserve.proc != nullptr);
	assert(opts->tbl_backing.proc  != nullptr);
	str8cache__init__u(u8_(cache), u8_(opts));
}

I_ Str8Cache str8cache__make(Opts_str8cache_init*R_ opts) { Str8Cache cache; str8cache__init(& cache, opts); return cache; }

S_ void str8cache_clear__u(U8 kt) {
	uvar(KT1CX_ByteMeta, meta) = {0};
	str8cache__fill_byte_meta__u(u8_(meta));
	kt1cx_clear__u(kt, u8_(meta));
}

S_ U8 str8cache_get__u(U8 kt, U8 key) {
	uvar(KT1CX_ByteMeta, meta) = {0};
	str8cache__fill_byte_meta__u(u8_(meta));
	return kt1cx_get__u(kt, key, u8_(meta));
}

S_ U8 str8cache_set__u(U8 kt, U8 key, U8 value_str, U8 str_reserve, U8 backing_cells) {
	assert(value_str != null);
	U8 value_ptr = u8_r(value_str + Str8_ptr)[0];
	U8 value_len = u8_r(value_str + Str8_len)[0];
	assert(value_ptr != null);
	uvar(KT1CX_ByteMeta, meta) = {0};
	str8cache__fill_byte_meta__u(u8_(meta));
	U8 entry = kt1cx_set__u(kt, key, value_ptr, value_len, backing_cells, u8_(meta));
	if (entry == null) { return null; }
	U8 stored      = entry + KT1CX_Slot_Str8_value;
	U8 stored_ptr  = u8_r(stored + Str8_ptr)[0];
	U8 stored_len  = u8_r(stored + Str8_len)[0];
	U8 reserve_proc = u8_r(str_reserve + AllocatorInfo_proc)[0];
	U8 reserve_data = u8_r(str_reserve + AllocatorInfo_data)[0];
	assert(reserve_proc != null);
	if (stored_ptr == 0 || stored_len < value_len) {
		uvar(Slice_Mem, allocation);
		mem__alloc__u(u8_(allocation), reserve_proc, reserve_data, value_len, 0, 1);
		stored_ptr = u8_r(u8_(allocation) + Slice_ptr)[0];
		stored_len = u8_r(u8_(allocation) + Slice_len)[0];
		u8_r(stored + Str8_ptr)[0] = stored_ptr;
		u8_r(stored + Str8_len)[0] = stored_len;
	}
	mem_copy(stored_ptr, value_ptr, value_len);
	u8_r(stored + Str8_len)[0] = value_len;
	return stored;
}

S_ void cache_str8__u(U8 result, U8 cache, U8 str) {
	assert(result != null);
	assert(cache  != null);
	assert(str    != null);
	U8 hash = 0;
	U8 str_ptr = u8_r(str + Str8_ptr)[0];
	U8 str_len = u8_r(str + Str8_len)[0];
	hash64_fnv1a__u(u8_(& hash), str_ptr, str_len, 0);
	U8 entry = str8cache_set__u(
		cache + Str8Cache_kt + KT1CX_Str8_table,
		hash,
		str,
		cache + Str8Cache_str_reserve,
		cache + Str8Cache_cell_reserve
	);
	if (entry == null) {
		u8_r(result + Str8_ptr)[0] = 0;
		u8_r(result + Str8_len)[0] = 0;
		return;
	}
	u8_r(result + Str8_ptr)[0] = u8_r(entry + Str8_ptr)[0];
	u8_r(result + Str8_len)[0] = u8_r(entry + Str8_len)[0];
}

I_ void str8cache_clear(KT1CX_Str8 kt) {
	kt1cx_assert(kt);
	str8cache_clear__u(u8_(& kt.table));
}

I_ Str8* str8cache_get(KT1CX_Str8 kt, U8 key) {
	kt1cx_assert(kt);
	return cast(Str8*, str8cache_get__u(u8_(& kt.table), key));
}

I_ Str8* str8cache_set(KT1CX_Str8 kt, U8 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells) {
	kt1cx_assert(kt);
	slice_assert(value);
	assert(str_reserve.proc  != nullptr);
	assert(backing_cells.proc != nullptr);
	U8 entry = str8cache_set__u(
		u8_(& kt.table),
		key,
		u8_(& value),
		u8_(& str_reserve),
		u8_(& backing_cells)
	);
	assert(entry != null);
	return cast(Str8*, entry);
}

I_ Str8 cache_str8(Str8Cache_R cache, Str8 str) {
	Str8 result = {0};
	assert(cache != nullptr);
	slice_assert(str);
	cache_str8__u(u8_(& result), u8_(cache), u8_(& str));
	return result;
}

S_ void str8gen_init__u(U8 gen, U8 backing) {
	assert(gen     != null);
	assert(backing != null);
	assert(u8_r(backing + AllocatorInfo_proc)[0] != null);
	mem_copy(gen + Str8Gen_backing, backing, size_of(AllocatorInfo));
	U8 backing_proc = u8_r(backing + AllocatorInfo_proc)[0];
	U8 backing_data = u8_r(backing + AllocatorInfo_data)[0];
	uvar(Slice_Mem, buffer);
	mem__alloc__u(u8_(buffer), backing_proc, backing_data, kilo(4), 0, 1);
	u8_r(gen + Str8Gen_ptr)[0] = u8_r(u8_(buffer) + Slice_ptr)[0];
	u8_r(gen + Str8Gen_len)[0] = 0;
	u8_r(gen + Str8Gen_cap)[0] = u8_r(u8_(buffer) + Slice_len)[0];
}

I_ void str8gen_init(Str8Gen_R gen, AllocatorInfo backing) {
	assert(gen != nullptr);
	str8gen_init__u(u8_(gen), u8_(& backing));
}

I_ Str8Gen str8gen_make(AllocatorInfo backing) { Str8Gen gen; str8gen_init(& gen, backing); return gen; }

I_ Str8 str8_from_str8gen(Str8Gen gen) { return (Str8){ u8_(gen.ptr), gen.len }; }

S_ void str8gen_append_str8__u(U8 gen, U8 str_slice) {
	assert(gen       != null);
	assert(str_slice != null);
	U8 str_ptr = u8_r(str_slice + Str8_ptr)[0];
	U8 str_len = u8_r(str_slice + Str8_len)[0];
	U8 gen_ptr = u8_r(gen + Str8Gen_ptr)[0];
	U8 gen_len = u8_r(gen + Str8Gen_len)[0];
	U8 gen_cap = u8_r(gen + Str8Gen_cap)[0];
	U8 needed  = gen_len + str_len;
	U8 backing_proc = u8_r(gen + Str8Gen_backing + AllocatorInfo_proc)[0];
	U8 backing_data = u8_r(gen + Str8Gen_backing + AllocatorInfo_data)[0];
	assert(backing_proc != null);
	if (needed > gen_cap) {
		uvar(Slice_Mem, grown);
		mem__grow__u(u8_(grown), backing_proc, backing_data, gen_ptr, gen_cap, needed, 0, 1, true);
		gen_ptr = u8_r(u8_(grown) + Slice_ptr)[0];
		gen_cap = u8_r(u8_(grown) + Slice_len)[0];
		u8_r(gen + Str8Gen_ptr)[0] = gen_ptr;
		u8_r(gen + Str8Gen_cap)[0] = gen_cap;
	}
	mem_copy(gen_ptr + gen_len, str_ptr, str_len);
	u8_r(gen + Str8Gen_len)[0] = needed;
}

I_ void str8gen_append_str8(Str8Gen_R gen, Str8 str) {
	str8gen_append_str8__u(u8_(gen), u8_(& str));
}

S_ void str8gen__append_fmt__u(U8 gen, U8 fmt_slice, U8 entries_slice) {
	assert(gen != null);
	assert(fmt_slice != null);
	assert(entries_slice != null);
	Str8 formatted = {0};
	str8__fmt__u(u8_(& formatted), fmt_slice, entries_slice);
	str8gen_append_str8__u(gen, u8_(& formatted));
}

I_ void str8gen__append_fmt(Str8Gen_R gen, Str8 fmt_template, Slice_A2_Str8*R_ entries) {
	str8gen__append_fmt__u(u8_(gen), u8_(& fmt_template), u8_(entries));
}
#pragma endregion String Operations
#pragma endregion Key Table

#pragma region String Operations
#pragma endregion String Operations

#pragma region File System
#define MS_CREATE_ALWAYS         2
#define MS_OPEN_EXISTING         3
#define MS_GENERIC_READ          (0x80000000L)
#define MS_GENERIC_WRITE         (0x40000000L)
#define MS_FILE_SHARE_READ       0x00000001
#define MS_FILE_SHARE_WRITE      0x00000002
#define MS_FILE_ATTRIBUTE_NORMAL 0x00000080
#define MS_INVALID_FILE_SIZE     ((MS_DWORD)0xFFFFFFFF)
W_ MS_HANDLE ms_create_file_a(
	MS_LPCSTR                lpFileName,
	MS_DWORD                 dwDesiredAccess,
	MS_DWORD                 dwShareMode,
	MS_LPSECURITY_ATTRIBUTES lpSecurityAttributes,
	MS_DWORD                 dwCreationDisposition,
	MS_DWORD                 dwFlagsAndAttributes,
	MS_HANDLE                hTemplateFile) __asm__("CreateFileA");
W_ MS_BOOL ms_read_file(
	MS_HANDLE       hFile,
	MS_LPVOID       lpBuffer,
	MS_DWORD        nNumberOfBytesToRead,
	MS_LPDWORD      lpNumberOfBytesRead,
	MS_LPOVERLAPPED lpOverlapped) __asm__("ReadFile");
W_ MS_BOOL ms_write_file(
	MS_HANDLE       hFile,
	MS_LPCVOID      lpBuffer,
	MS_DWORD        nNumberOfBytesToWrite,
	MS_LPDWORD      lpNumberOfBytesWritten,
	MS_LPOVERLAPPED lpOverlapped) __asm__("WriteFile");
W_ MS_BOOL  ms_get_file_size_ex(MS_HANDLE hFile, MS_LARGE_INTEGER* lpFileSize) __asm__("GetFileSizeEx");
W_ MS_DWORD ms_get_last_error(void) __asm__("GetLastError");

S_ void file_read_contents__u(U8 path_ptr, U8 path_len, U8 backing_proc, U8 backing_data, B4 zero_backing, U8 result) {
	assert(result != null);
	slice_clear(result + FileOpInfo_content);
	assert(backing_proc != null);
	if (path_ptr == null || path_len == 0) {
		assert(false && "Invalid path");
		return;
	}

	LP_ B1 scratch[FILE_PATH_SCRATCH_CAP];
	U8 scratch_ptr = u8_(scratch);
	U8 scratch_cap = FILE_PATH_SCRATCH_CAP;
	U8 max_copy    = scratch_cap ? scratch_cap - 1 : 0;
	U8 copy_len    = path_len < max_copy ? path_len : max_copy;
	mem_copy(scratch_ptr, path_ptr, copy_len);
	u1_r(scratch_ptr)[copy_len] = 0;

	MS_HANDLE id_file = ms_create_file_a(
		cast(MS_LPCSTR, scratch_ptr),
		MS_GENERIC_READ,
		MS_FILE_SHARE_READ,
		null,
		MS_OPEN_EXISTING,
		MS_FILE_ATTRIBUTE_NORMAL,
		null
	);
	if (id_file == MS_INVALID_HANDLE_VALUE) {
		MS_DWORD error_code = ms_get_last_error();
		assert(error_code != 0);
		return;
	}

	MS_LARGE_INTEGER file_size = {0};
	if (! ms_get_file_size_ex(id_file, & file_size)) {
		ms_close_handle(id_file);
		return;
	}
	U8 desired_size = cast(U8, file_size.QuadPart);
	uvar(Slice_Mem, buffer);
	mem__alloc__u(u8_(buffer), backing_proc, backing_data, desired_size, 0, /*no_zero*/1);
	U8 buffer_ptr = u8_r(u8_(buffer) + Slice_ptr)[0];
	U8 buffer_len = u8_r(u8_(buffer) + Slice_len)[0];
	if (buffer_ptr == 0 || buffer_len < file_size.QuadPart) {
		ms_close_handle(id_file);
		return;
	}
	if (zero_backing) {
		mem_zero(buffer_ptr, buffer_len);
	}

	MS_DWORD amount_read = 0;
	MS_BOOL  read_result = ms_read_file(
		id_file,
		cast(MS_LPVOID, buffer_ptr),
		cast(MS_DWORD, desired_size),
		u8_(& amount_read),
		null
	);
	ms_close_handle(id_file);
	if (!read_result || amount_read != cast(MS_DWORD, desired_size)) {
		return;
	}
	slice_assign_comp(result + FileOpInfo_content, buffer_ptr, desired_size);
}

I_ FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents*R_ opts) {
	assert(opts != nullptr);
	assert(opts->backing.proc != nullptr);
	FileOpInfo info = {0};
	file_read_contents__u(path.ptr, path.len, u8_(opts->backing.proc), opts->backing.data, opts->zero_backing, u8_(& info));
	return info;
}

S_ void file_write_str8__u(U8 path_ptr, U8 path_len, U8 content_ptr, U8 content_len) {
	if (path_ptr == null || path_len == 0) {
		assert(false && "Invalid path");
		return;
	}
	if (content_ptr == null) {
		assert(false && "Invalid content");
		return;
	}

	LP_ B1 scratch[FILE_PATH_SCRATCH_CAP] = {0};
	U8 scratch_ptr = u8_(scratch);
	U8 scratch_cap = FILE_PATH_SCRATCH_CAP;
	U8 max_copy    = scratch_cap ? scratch_cap - 1 : 0;
	U8 copy_len    = path_len < max_copy ? path_len : max_copy;
	mem_copy(scratch_ptr, path_ptr, copy_len);
	u1_r(scratch_ptr)[copy_len] = 0;

	MS_HANDLE id_file = ms_create_file_a(
		cast(MS_LPCSTR, scratch_ptr),
		MS_GENERIC_WRITE,
		MS_FILE_SHARE_READ,
		null,
		MS_CREATE_ALWAYS,
		MS_FILE_ATTRIBUTE_NORMAL,
		null
	);
	if (id_file == MS_INVALID_HANDLE_VALUE) {
		MS_DWORD error_code = ms_get_last_error();
		assert(error_code != 0);
		return;
	}
	MS_DWORD bytes_written = 0;
	MS_BOOL  status = ms_write_file(
		id_file,
		cast(MS_LPCVOID, content_ptr),
		cast(MS_DWORD, content_len),
		u8_(& bytes_written),
		null
	);
	ms_close_handle(id_file);
	assert(status != 0);
	assert(bytes_written == content_len);
}

I_ void file_write_str8(Str8 path, Str8 content) {
	file_write_str8__u(path.ptr, path.len, content.ptr, content.len);
}
#pragma endregion File System

#pragma region WATL
#define WATL_ALLOC_STRUCT(dest, proc, data, type, zero)                                         \
	do {                                                                                        \
		uvar(Slice_Mem, _alloc_slice);                                                          \
		mem__alloc__u(u8_(_alloc_slice), proc, data, size_of(type), alignof(type), zero);      \
		dest = u8_r(u8_(_alloc_slice) + Slice_ptr)[0];                                         \
	} while (0)

S_ void watl_lex__u(U8 info, U8 source, U8 opts) {
	if (info == null || source == null || opts == null) { return; }
	U8 src_ptr = u8_r(source + Str8_ptr)[0];
	U8 src_len = u8_r(source + Str8_len)[0];
	if (src_len == 0) { return; }

	U8 ainfo_msgs = opts + Opts_watl_lex_ainfo_msgs;
	U8 ainfo_toks = opts + Opts_watl_lex_ainfo_toks;
	U8 msgs_proc = u8_r(ainfo_msgs + AllocatorInfo_proc)[0]; assert(msgs_proc != null);
	U8 msgs_data = u8_r(ainfo_msgs + AllocatorInfo_data)[0];
	U8 toks_proc = u8_r(ainfo_toks + AllocatorInfo_proc)[0]; assert(toks_proc != null);
	U8 toks_data = u8_r(ainfo_toks + AllocatorInfo_data)[0];
	U8 fail_slice = u1_r(opts + Opts_watl_lex_failon_slice_constraint_fail)[0];

	u8_r(info + WATL_LexInfo_msgs)[0] = 0;
	u8_r(info + WATL_LexInfo_toks + Slice_ptr)[0] = 0;
	u8_r(info + WATL_LexInfo_toks + Slice_len)[0] = 0;
	u4_r(info + WATL_LexInfo_signal)[0] = 0;

	U8 msg_last = 0;
	U8 first_tok = 0;
	U8 tok = 0;
	U8 tok_count = 0;
	B4 was_formatting = true;

	U8 cursor = src_ptr;
	U8 end    = src_ptr + src_len;
	U1 prev_code = 0;

#define WATL_ALLOC_TOK(dest) WATL_ALLOC_STRUCT(dest, toks_proc, toks_data, WATL_Tok, 1)
#define WATL_ALLOC_LEX_MSG(dest) WATL_ALLOC_STRUCT(dest, msgs_proc, msgs_data, WATL_LexMsg, 0)

	while (cursor < end) {
		U1 code = u1_r(cursor)[0];
		switch (code) {
		case WATL_Tok_Space:
		case WATL_Tok_Tab: {
			if (tok == 0 || prev_code != code) {
				U8 new_tok = 0;
				WATL_ALLOC_TOK(new_tok);
				if (tok != 0 && new_tok != tok + size_of(WATL_Tok)) { goto slice_constraint_fail; }
				tok = new_tok;
				if (first_tok == 0) { first_tok = tok; }
				u8_r(tok + Str8_ptr)[0] = cursor;
				u8_r(tok + Str8_len)[0] = 0;
				was_formatting = true;
				++ tok_count;
			}
			cursor += 1;
			u8_r(tok + Str8_len)[0] += 1;
		} break;

		case WATL_Tok_LineFeed: {
			U8 new_tok = 0;
			WATL_ALLOC_TOK(new_tok);
			if (tok != 0 && new_tok != tok + size_of(WATL_Tok)) { goto slice_constraint_fail; }
			tok = new_tok;
			if (first_tok == 0) { first_tok = tok; }
			u8_r(tok + Str8_ptr)[0] = cursor;
			u8_r(tok + Str8_len)[0] = 1;
			cursor += 1;
			was_formatting = true;
			++ tok_count;
		} break;

		case WATL_Tok_CarriageReturn: {
			U8 new_tok = 0;
			WATL_ALLOC_TOK(new_tok);
			if (tok != 0 && new_tok != tok + size_of(WATL_Tok)) { goto slice_constraint_fail; }
			tok = new_tok;
			if (first_tok == 0) { first_tok = tok; }
			U8 advance = ((cursor + 1) < end && u1_r(cursor + 1)[0] == WATL_Tok_LineFeed) ? 2 : 1;
			u8_r(tok + Str8_ptr)[0] = cursor;
			u8_r(tok + Str8_len)[0] = advance;
			cursor += advance;
			was_formatting = true;
			++ tok_count;
		} break;

		default: {
			if (was_formatting || tok == 0) {
				U8 new_tok = 0;
				WATL_ALLOC_TOK(new_tok);
				if (tok != 0 && new_tok != tok + size_of(WATL_Tok)) { goto slice_constraint_fail; }
				tok = new_tok;
				if (first_tok == 0) { first_tok = tok; }
				u8_r(tok + Str8_ptr)[0] = cursor;
				u8_r(tok + Str8_len)[0] = 0;
				was_formatting = false;
				++ tok_count;
			}
			cursor += 1;
			u8_r(tok + Str8_len)[0] += 1;
		} break;
		}
		prev_code = code;
	}

	if (first_tok == 0) { return; }
	u8_r(info + WATL_LexInfo_toks + Slice_ptr)[0] = first_tok;
	u8_r(info + WATL_LexInfo_toks + Slice_len)[0] = tok_count;
	return;

slice_constraint_fail: {
	u4_r(info + WATL_LexInfo_signal)[0] |= WATL_LexStatus_MemFail_SliceConstraintFail;
	U8 msg = 0;
	WATL_ALLOC_LEX_MSG(msg);
	u8_r(msg + WATL_LexMsg_next)[0] = 0;
	Str8 msg_content = lit("Token slice allocation was not contiguous");
	u8_r(msg + WATL_LexMsg_content + Str8_ptr)[0] = msg_content.ptr;
	u8_r(msg + WATL_LexMsg_content + Str8_len)[0] = msg_content.len;
	u8_r(msg + WATL_LexMsg_tok)[0] = tok;
	u4_r(msg + WATL_LexMsg_pos + WATL_Pos_line)[0]   = cast(U4, -1);
	u4_r(msg + WATL_LexMsg_pos + WATL_Pos_column)[0] = cast(U4, -1);
	if (u8_r(info + WATL_LexInfo_msgs)[0] == 0) {
		u8_r(info + WATL_LexInfo_msgs)[0] = msg;
	} else {
		u8_r(msg_last + WATL_LexMsg_next)[0] = msg;
	}
	msg_last = msg;
	assert(fail_slice == false);
	return;
}
#undef WATL_ALLOC_TOK
#undef WATL_ALLOC_LEX_MSG
#undef WATL_ALLOC_STRUCT
}

I_ void api_watl_lex(WATL_LexInfo_R info, Str8 source, Opts_watl_lex*R_ opts) {
	assert(info  != nullptr);
	assert(opts  != nullptr);
	watl_lex__u(u8_(info), u8_(& source), u8_(opts));
}

I_ WATL_LexInfo watl__lex(Str8 source, Opts_watl_lex*R_ opts) {
	WATL_LexInfo info = {0};
	api_watl_lex(& info, source, opts);
	return info;
}

S_ void watl_parse__u(U8 info, U8 tokens, U8 opts) {
	(void)info; (void)tokens; (void)opts;
}

I_ void api_watl_parse(WATL_ParseInfo_R info, Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts) {
	assert(info != nullptr);
	assert(opts != nullptr);
	watl_parse__u(u8_(info), u8_(& tokens), u8_(opts));
}

I_ WATL_ParseInfo watl__parse(Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts) {
	WATL_ParseInfo info = {0};
	api_watl_parse(& info, tokens, opts);
	return info;
}

S_ void watl_dump_listing__u(U8 result, U8 buffer_ainfo, U8 lines) {
	(void)result; (void)buffer_ainfo; (void)lines;
}

I_ Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines) {
	Str8 out = {0};
	watl_dump_listing__u(u8_(& out), u8_(& buffer), u8_(& lines));
	return out;
}
#pragma endregion WATL

#pragma region Debug
#if defined(BUILD_DEBUG)
// #include <stdio.h>
#define MS_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS (*__local_stdio_printf_options())
#define MS_stderr                          (__acrt_iob_func(2))
#define MS__crt_va_start_a(ap, x)          ((void)(__va_start(&ap, x)))
#define MS__crt_va_arg(ap, t)                                          \
	((sizeof(t) > sizeof(__int64) || (sizeof(t) & (sizeof(t) - 1)) != 0) \
		? **(t**)((ap += sizeof(__int64)) - sizeof(__int64))               \
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
N_ U8* __cdecl __local_stdio_printf_options(void) {
	// NOTE(CRT): This function must not be inlined into callers to avoid ODR violations.  The
	// static local variable has different names in C and in C++ translation units.
	LP_ U8 _OptionsStorage; return &_OptionsStorage;
}
int __cdecl __stdio_common_vfprintf_s(
	U8               _Options,
	MS_FILE*         _Stream,
	char const*      _Format,
	_locale_t        _Locale,
	va_list          _ArgList
);
void __cdecl __va_start(va_list* , ...);
I_ int printf_err(char const* fmt, ...) {
	int result;
	va_list args;
	va_start(args, fmt);
	result = __stdio_common_vfprintf_s(MS_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS, MS_stderr, fmt, nullptr, args);
	va_end(args);
	return result;
}
S_ inline void assert_handler( UTF8*R_ condition, UTF8*R_ file, UTF8*R_ function, S4 line, UTF8*R_ msg, ... ) {
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
#pragma endregion WATL

#pragma endregion Implementation

int main(void)
{
	os_init();
	VArena_R vm_file = varena_make(.reserve_size = giga(4), .flags = VArenaFlag_NoLargePages);
	// FileOpInfo file  = file_read_contents(lit("watl.v0.llvm.lottes.c"), .backing = ainfo_varena(vm_file));
	// slice_assert(file.content);

	Arena_R a_msgs = arena_make();
	Arena_R a_toks = arena_make();
	// WATL_LexInfo lex_res = watl_lex(pcast(Str8, file.content),
	// 	.ainfo_msgs = ainfo_arena(a_msgs),
	// 	.ainfo_toks = ainfo_arena(a_toks),
	// );
	// assert((lex_res.signal & WATL_LexStatus_MemFail_SliceConstraintFail) == 0);

	// Arena_R str_cache_kt1_ainfo = arena_make();
	// Str8Cache str_cache = str8cache_make(
	// 	.str_reserve    = ainfo_arena(arena_make(.reserve_size = mega(256))),
	// 	.cell_reserve   = ainfo_arena(str_cache_kt1_ainfo),
	// 	.tbl_backing    = ainfo_arena(str_cache_kt1_ainfo),
	// 	.cell_pool_size = kilo(8),
	// 	.table_size     = kilo(64),
	// );

	// Arena_R a_lines = arena_make();
	// WATL_ParseInfo parse_res = watl_parse(lex_res.toks,
	// 	.ainfo_msgs  = ainfo_arena(a_msgs),
	// 	.ainfo_nodes = ainfo_arena(a_toks),
	// 	.ainfo_lines = ainfo_arena(a_lines),
	// 	.str_cache   = & str_cache
	// );
	//assert((parse_res.signal & WATL_ParseStatus_MemFail_SliceConstraintFail) == 0);

	// arena_reset(a_msgs);
	// arena_reset(a_toks);
	// Str8 listing = watl_dump_listing(ainfo_arena(a_msgs), parse_res.lines);
	// file_write_str8(lit("watl.v0.lottes.c.listing.txt"), listing);
	// return 0;
}

#pragma clang diagnostic pop
