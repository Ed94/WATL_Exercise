/*
WATL Exercise
Version:   0 (From Scratch, 1-Stage Compilation, LLVM & WinAPI Only, Win CRT Multi-threaded Static Linkage)
Host:      Windows 11 (x86-64)
Toolchain: LLVM (2025-08-30), C-Stanard: 11

Based on: Neokineogfx - Fixing C, personalized to include typeinfo more readily.
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
#define align_(value)     __attribute__((aligned (value)))             // for easy alignment
#define expect_(x, y)     __builtin_expect(x, y)                       // so compiler knows the common path
#define finline           static inline __attribute__((always_inline)) // force inline
#define no_inline         static        __attribute__((noinline))      // force no inline [used in thread api]
#define R_                __restrict                                   // pointers are either restricted or volatile and nothing else 
#define V_                volatile                                     // pointers are either restricted or volatile and nothing else
#define W_                __attribute((__stdcall__)) __attribute__((__force_align_arg_pointer__))

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

typedef __UINT8_TYPE__  def_tset(U1); typedef __UINT16_TYPE__ def_tset(U2); typedef __UINT32_TYPE__ def_tset(U4); typedef __UINT64_TYPE__ def_tset(U8);
typedef __INT8_TYPE__   def_tset(S1); typedef __INT16_TYPE__  def_tset(S2); typedef __INT32_TYPE__  def_tset(S4); typedef __INT64_TYPE__  def_tset(S8);
typedef unsigned char   def_tset(B1); typedef __UINT16_TYPE__ def_tset(B2); typedef __UINT32_TYPE__ def_tset(B4); typedef __UINT64_TYPE__ def_tset(B8);
typedef float           def_tset(F4); 
typedef double          def_tset(F8);
typedef float  V4_F4 __attribute__((vector_size(16))); typedef def_ptr_set(V4_F4);
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

// Signed stuff (still diff flavor from Lottes)

#define sop_1(op, a, b) cast(U1, s1_(a) op s1_(b))
#define sop_2(op, a, b) cast(U2, s2_(a) op s2_(b))
#define sop_4(op, a, b) cast(U4, s4_(a) op s4_(b))
#define sop_8(op, a, b) cast(U8, s8_(a) op s8_(b))

#define def_signed_op(id, op, width) finline U ## width id ## _s ## width(U ## width a, U ## width b) {return sop_ ## width(op, a, b); }
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

finline U4 atm_add_u4 (U4_R a, U4 v){__asm__ volatile("lock xaddl %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
finline U8 atm_add_u8 (U8_R a, U8 v){__asm__ volatile("lock xaddq %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
finline U4 atm_swap_u4(U4_R a, U4 v){__asm__ volatile("lock xchgl %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
finline U8 atm_swap_u8(U8_R a, U8 v){__asm__ volatile("lock xchgq %0,%1":"=r"(v),"=m"(*a):"0"(v),"m"(*a):"memory","cc");return v;}
 
finline void barrier_compiler(void){__asm__ volatile("::""memory");} // Compiler Barrier
finline void barrier_memory  (void){__builtin_ia32_mfence();}        // Memory   Barrier
finline void barrier_read    (void){__builtin_ia32_lfence();}        // Read     Barrier
finline void barrier_write   (void){__builtin_ia32_sfence();}        // Write    Barrier
#pragma endregion DSL

#pragma region Strings
typedef unsigned char def_tset(UTF8);
typedef def_struct(Str8)       { UTF8* ptr; U8 len; }; typedef Str8 def_tset(Slice_UTF8);
typedef def_struct(Slice_Str8) { Str8* ptr; U8 len; };
#define lit(string_literal)    (Str8){ (UTF8*) string_literal, size_of(string_literal) - 1 }
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

finline U8 mem_copy            (U8 dest, U8 src,   U8 len) { return (U8)(__builtin_memcpy ((void*)dest, (void const*)src,   len)); }
finline U8 mem_copy_overlapping(U8 dest, U8 src,   U8 len) { return (U8)(__builtin_memmove((void*)dest, (void const*)src,   len)); }
finline U8 mem_fill            (U8 dest, U8 value, U8 len) { return (U8)(__builtin_memset ((void*)dest, (int)        value, len)); }
finline B4 mem_zero            (U8 dest,           U8 len) { if (dest == 0) return false; mem_fill(dest, 0, len); return true; }

finline
U8 align_pow2(U8 x, U8 b) {
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

finline void slice__zero(Slice_B1 mem, U8 typewidth) { slice_assert(mem); mem_zero(u8_(mem.ptr), mem.len); }
#define slice_zero(slice) slice__zero(slice_mem_s(slice), size_of_slice_type(slice))

finline
void slice__copy(Slice_B1 dest, U8 dest_typewidth, Slice_B1 src, U8 src_typewidth) {
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
typedef void def_proc(AllocatorProc) (AllocatorProc_In In, AllocatorProc_Out_R Out);
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

finline AllocatorQueryInfo allocator_query(AllocatorInfo ainfo);

finline void        mem_free      (AllocatorInfo ainfo, Slice_Mem mem);
finline void        mem_reset     (AllocatorInfo ainfo);
finline void        mem_rewind    (AllocatorInfo ainfo, AllocatorSP save_point);
finline AllocatorSP mem_save_point(AllocatorInfo ainfo);

typedef def_struct(Opts_mem_alloc)  { U8 alignment; B4 no_zero; A4_B1 _PAD_; };
typedef def_struct(Opts_mem_grow)   { U8 alignment; B4 no_zero; B4 give_actual; };
typedef def_struct(Opts_mem_shrink) { U8 alignment; };
typedef def_struct(Opts_mem_resize) { U8 alignment; B4 no_zero; B4 give_actual; };

finline Slice_Mem mem__alloc (AllocatorInfo ainfo,                U8 size, Opts_mem_alloc_R  opts);
finline Slice_Mem mem__grow  (AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow_R   opts);
finline Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize_R opts);
finline Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink_R opts);

#define mem_alloc(ainfo, size, ...)       mem__alloc (ainfo,      size, opt_args(Opts_mem_alloc,  __VA_ARGS__))
#define mem_grow(ainfo,   mem, size, ...) mem__grow  (ainfo, mem, size, opt_args(Opts_mem_grow,   __VA_ARGS__))
#define mem_resize(ainfo, mem, size, ...) mem__resize(ainfo, mem, size, opt_args(Opts_mem_resize, __VA_ARGS__))
#define mem_shrink(ainfo, mem, size, ...) mem__shrink(ainfo, mem, size, opt_args(Opts_mem_shrink, __VA_ARGS__))

#define alloc_type(ainfo, type, ...)       (type*)                    mem__alloc(ainfo, size_of(type),        opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr
#define alloc_slice(ainfo, type, num, ...) (tmpl(Slice,type)){ (type*)mem__alloc(ainfo, size_of(type) * num,  opt_args(Opts_mem_alloc, __VA_ARGS__)).ptr, num }
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
finline FArena      farena_make  (Slice_Mem mem);
finline void        farena_init  (FArena_R arena, Slice_Mem byte);
        Slice_Mem   farena__push (FArena_R arena, U8 amount, U8 type_width, Opts_farena*R_ opts);
finline void        farena_reset (FArena_R arena);
finline void        farena_rewind(FArena_R arena, AllocatorSP save_point);
finline AllocatorSP farena_save  (FArena  arena);

void farena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out_R out);
#define ainfo_farena(arena) (AllocatorInfo){ .proc = farena_allocator_proc, .data = u8_(& arena) }

#define farena_push_mem(arena, amount, ...) farena__push(arena, amount, 1, opt_args(Opts_farena, lit(stringify(B1)), __VA_ARGS__))

#define farena_push(arena, type, ...) \
cast(type*, farena__push(arena, size_of(type), 1, opt_args(Opts_farena, lit(stringify(type)), __VA_ARGS__))).ptr

#define farena_push_array(arena, type, amount, ...) \
(Slice ## type){ farena__push(arena, size_of(type), amount, opt_args(Opts_farena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion FArena

#pragma region OS
finline U8   clock(void){U8 aa,dd;__asm__ volatile("rdtsc":"=a"(aa),"=d"(dd));return aa;}
finline void pause(void){__asm__ volatile("pause":::"memory");}

typedef def_struct(OS_SystemInfo) {
	U8 target_page_size;
};
typedef def_struct(Opts_vmem) {
	U8    base_addr;
	B4    no_large_pages;
	A4_B1 _PAD_;
};
void os_init(void);
finline OS_SystemInfo* os_system_info(void);

finline B4   os__vmem_commit (U8 vm, U8 size, Opts_vmem*R_ opts);
finline U8   os__vmem_reserve(       U8 size, Opts_vmem*R_ opts);
finline void os_vmem_release (U8 vm, U8 size);

#define os_vmem_reserve(size, ...)    os__vmem_reserve(    size, opt_args(Opts_vmem, __VA_ARGS__))
#define os_vmem_commit(vm, size, ...) os__vmem_commit (vm, size, opt_args(Opts_vmem, __VA_ARGS__))
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
VArena*   varena__make(Opts_varena_make*R_ opts);
#define   varena_make(...) varena__make(opt_args(Opts_varena_make, __VA_ARGS__))

        Slice_Mem   varena__push  (VArena_R arena, U8 amount, U8 type_width, Opts_varena*R_ opts);
finline void        varena_release(VArena_R arena);
finline void        varena_rewind (VArena_R arena, AllocatorSP save_point);
        void        varena_reset  (VArena_R arena);
        Slice_Mem   varena__shrink(VArena_R arena, Slice_Mem old_allocation, U8 requested_size);
finline AllocatorSP varena_save   (VArena_R arena);

void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out_R out);
#define ainfo_varena(varena) (AllocatorInfo) { .proc = & varena_allocator_proc, .data = u8_(varena) }

#define varena_push_mem(arena, amount, ...) varena__push(arena, amount, 1, opt_args(Opts_varena, lit(stringify(B1)), __VA_ARGS__))

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
        Arena*      arena__make  (Opts_arena_make*R_ opts);
        Slice_Mem   arena__push  (Arena_R arena, U8 amount, U8 type_width, Opts_arena*R_ opts);
finline void        arena_release(Arena_R arena);
finline void        arena_reset  (Arena_R arena);
        void        arena_rewind (Arena_R arena, AllocatorSP save_point);
finline AllocatorSP arena_save   (Arena_R arena);

void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out_R out);
#define ainfo_arena(arena) (AllocatorInfo){ .proc = & arena_allocator_proc, .data = u8_(arena) }

#define arena_make(...) arena__make(opt_args(Opts_arena_make, __VA_ARGS__))

#define arena_push_mem(arena, amount, ...) arena__push(arena, amount, 1, opt_args(Opts_arena, lit(stringify(B1)), __VA_ARGS__))

#define arena_push(arena, type, ...) \
cast(type*, arena__push(arena, 1, size_of(type), opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__) ).ptr)

#define arena_push_array(arena, type, amount, ...) \
(tmpl(Slice,type)){ arena__push(arena, size_of(type), amount, opt_args(Opts_arena, lit(stringify(type)), __VA_ARGS__)).ptr, amount }
#pragma endregion Arena

#pragma region Hashing
typedef def_struct(Opts_hash64_fnv1a) { U8 seed; };
finline
void hash64__fnv1a(U8_R hash, Slice_Mem data, Opts_hash64_fnv1a*R_ opts) {
	local_persist U8 const default_seed = 0xcbf29ce484222325; 
	assert(opts != nullptr); if (opts->seed == 0) opts->seed = default_seed;
	hash[0] = opts->seed;
	U8 elem = data.ptr;
loop:
	if (elem == slice_end(data)) goto end;
	hash[0] ^= u1_r(elem)[0];
	hash[0] *= 0x100000001b3;
	elem    += 1;
	goto loop;
end:
	return;
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
void ktl_populate_slice_a2_str8(KTL_Str8*R_ kt, AllocatorInfo backing, Slice_A2_Str8 values);
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
        void kt1cx_init   (KT1CX_Info info, KT1CX_InfoMeta m, KT1CX_Byte*R_ result);
        void kt1cx_clear  (KT1CX_Byte kt,          KT1CX_ByteMeta meta);
finline U8   kt1cx_slot_id(KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
        U8   kt1cx_get    (KT1CX_Byte kt,  U8 key, KT1CX_ByteMeta meta);
        U8   kt1cx_set    (KT1CX_Byte kt,  U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta meta);

#define kt1cx_assert(kt) do { \
	slice_assert(kt.table);     \
} while(0)
#define kt1cx_byte(kt) (KT1CX_Byte){ (Slice_Mem){u8_(kt.table.ptr), kt.table.len} }
#pragma endregion KT1CX

#pragma region String Operations
finline B4 char_is_upper(U1 c) { return('A' <= c && c <= 'Z'); }
finline U1 char_to_lower(U1 c) { if (char_is_upper(c)) { c += ('a' - 'A'); } return(c); }
finline U1 integer_symbols(U1 value) {
	local_persist U1 lookup_table[16] = { '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F', }; return lookup_table[cast(U1, value)]; 
}

finline char* str8_to_cstr_capped(Str8 content, Slice_Mem mem);
Str8  str8_from_u32(AllocatorInfo ainfo, U4 num, U4 radix, U4 min_digits, U4 digit_group_separator);

finline Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8*R_ entries);
#define str8_fmt_backed(tbl_backing, buf_backing, fmt_template, ...) \
str8__fmt_backed(tbl_backing, buf_backing, lit(fmt_template), slice_arg_from_array(A2_Str8, __VA_ARGS__))

Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8*R_ entries);
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
        void      str8cache__init(Str8Cache_R cache, Opts_str8cache_init*R_ opts);
finline Str8Cache str8cache__make(                   Opts_str8cache_init*R_ opts);

#define str8cache_init(cache, ...) str8cache__init(cache, opt_args(Opts_str8cache_init, __VA_ARGS__))
#define str8cache_make(...)        str8cache__make(       opt_args(Opts_str8cache_init, __VA_ARGS__))

finline void  str8cache_clear(KT1CX_Str8 kt);
finline Str8* str8cache_get(KT1CX_Str8 kt, U8 key);
finline Str8* str8cache_set(KT1CX_Str8 kt, U8 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells);

finline Str8 cache_str8(Str8Cache_R cache, Str8 str);

typedef def_struct(Str8Gen) {
	AllocatorInfo backing;
	UTF8* ptr;
	U8    len;
	U8    cap;
};
finline void    str8gen_init(Str8Gen_R gen, AllocatorInfo backing);
finline Str8Gen str8gen_make(               AllocatorInfo backing);

#define str8gen_slice_mem(gen) slice_mem_s(gen)

finline Str8 str8_from_str8gen(Str8Gen gen) { return (Str8){ cast(UTF8_R, gen.ptr), gen.len}; }

finline void str8gen_append_str8(Str8Gen_R gen, Str8 str);
        void str8gen__append_fmt(Str8Gen_R gen, Str8 fmt_template, Slice_A2_Str8*R_ tokens);

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
void api_file_read_contents(FileOpInfo_R result, Str8 path, Opts_read_file_contents opts);
void file_write_str8       (Str8 path, Str8 content);

finline FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents*R_ opts);
#define file_read_contents(path, ...) file__read_contents(path, opt_args(Opts_read_file_contents, __VA_ARGS__))
#pragma endregion File System

#pragma region WATL
typedef def_enum(U4, WATL_TokKind) {
	WATL_Tok_Space          = ' ',
	WATL_Tok_Tab            = '\t',
	WATL_Tok_CarriageReturn = '\r',
	WATL_Tok_LineFeed       = '\n',
	WATL_Tok_Text           = 0xFFFFFFF,
};
typedef Str8 def_tset(WATL_Tok);
typedef def_Slice(WATL_Tok);
typedef def_enum(U4, WATL_LexStatus) {
	WATL_LexStatus_MemFail_SliceConstraintFail = (1 << 0),
};
typedef def_struct(WATL_Pos) {
	S4 line;
	S4 column;
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
void         api_watl_lex(WATL_LexInfo_R info, Str8 source, Opts_watl_lex*R_ opts);
WATL_LexInfo watl__lex   (                     Str8 source, Opts_watl_lex*R_ opts);
#define watl_lex(source, ...) watl__lex(source, opt_args(Opts_watl_lex, __VA_ARGS__))

typedef Str8 WATL_Node; typedef def_ptr_set(WATL_Node);
typedef def_Slice(WATL_Node);
typedef Slice_WATL_Node def_tset(WATL_Line);
typedef def_Slice(WATL_Line);
typedef def_struct(WATL_ParseMsg) {
	WATL_ParseMsg* next;
	Str8        content;
	WATL_Line*  line;
	WATL_Tok*   tok;
	WATL_Pos    pos;
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
	B4 failon_slice_constraint_fail;
	A4_B1 _PAD_;
};
void           api_watl_parse(WATL_ParseInfo_R info, Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts);
WATL_ParseInfo watl__parse   (                       Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts);
#define watl_parse(tokens, ...) watl__parse(tokens, opt_args(Opts_watl_parse, __VA_ARGS__))

Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines);
#pragma endregion WATL

#pragma endregion Header

#pragma region Implementation

#pragma region Allocator Interface
finline
AllocatorQueryInfo allocator_query(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	AllocatorQueryInfo out; ainfo.proc((AllocatorProc_In){ .data = ainfo.data, .op = AllocatorOp_Query}, (AllocatorProc_Out_R)& out); 
	return out;
}
finline
void mem_free(AllocatorInfo ainfo, Slice_Mem mem) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Free, .old_allocation = mem}, &(AllocatorProc_Out){});
}
finline
void mem_reset(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Reset}, &(AllocatorProc_Out){});
}
finline
void mem_rewind(AllocatorInfo ainfo, AllocatorSP save_point) {
	assert(ainfo.proc != nullptr);
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_Rewind, .save_point = save_point}, &(AllocatorProc_Out){});
}
finline
AllocatorSP mem_save_point(AllocatorInfo ainfo) {
	assert(ainfo.proc != nullptr);
	AllocatorProc_Out out;
	ainfo.proc((AllocatorProc_In){.data = ainfo.data, .op = AllocatorOp_SavePoint}, & out);
	return out.save_point;
}
finline
Slice_Mem mem__alloc(AllocatorInfo ainfo, U8 size, Opts_mem_alloc*R_ opts) {
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
finline
Slice_Mem mem__grow(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_grow*R_ opts) {
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
	return (Slice_Mem){ out.allocation.ptr, opts->give_actual ? out.allocation.len : in.requested_size };
}
finline
Slice_Mem mem__resize(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_resize*R_ opts) {
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
	return (Slice_Mem){ out.allocation.ptr, opts->give_actual ? out.allocation.len : in.requested_size };
}
finline
Slice_Mem mem__shrink(AllocatorInfo ainfo, Slice_Mem mem, U8 size, Opts_mem_shrink*R_ opts) {
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
finline
void farena_init(FArena_R arena, Slice_Mem mem) {
	assert(arena != nullptr);
	arena->start    = mem.ptr;
	arena->capacity = mem.len;
	arena->used     = 0;
}
finline FArena farena_make(Slice_Mem mem) { FArena a; farena_init(& a, mem); return a; }
inline
Slice_Mem farena__push(FArena_R arena, U8 amount, U8 type_width, Opts_farena*R_ opts) {
	assert(opts != nullptr);
	if (amount == 0) { return (Slice_Mem){}; }
	U8 desired   = type_width * amount;
	U8 to_commit = align_pow2(desired, opts->alignment ?  opts->alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8 unused    = arena->capacity - arena->used; assert(to_commit <= unused);
	U8 ptr       = arena->start + arena->used;
	arena->used += to_commit;
	return (Slice_Mem){ptr, desired};
}
inline
Slice_Mem farena__grow(FArena_R arena, Slice_Mem old_allocation, U8 requested_size, U8 alignment, B4 should_zero) {
	// Check if the allocation is at the end of the arena
	U8 alloc_end = old_allocation.ptr + old_allocation.len;
	U8 arena_end = arena->start + arena->used;
	if (alloc_end != arena_end) {
		// Not at the end, can't grow in place
		return (Slice_Mem){0};
	}
	// Calculate growth
	U8 grow_amount  = requested_size - old_allocation.len;
	U8 aligned_grow = align_pow2(grow_amount, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	U8 unused       = arena->capacity - arena->used;
	if (aligned_grow > unused) {
		// Not enough space
		return (Slice_Mem){0};
	}
	arena->used += aligned_grow;
	Slice_Mem result = (Slice_Mem){ old_allocation.ptr, aligned_grow + requested_size };
	mem_zero(old_allocation.ptr + old_allocation.len, grow_amount * cast(U8, should_zero));
	return result;
}
inline
Slice_Mem farena__shrink(FArena_R arena, Slice_Mem old_allocation, U8 requested_size, U8 alignment)
{
	// Check if the allocation is at the end of the arena
	U8 alloc_end = old_allocation.ptr + old_allocation.len;
	U8 arena_end = arena->start + arena->used;
	if (alloc_end != arena_end) {
		// Not at the end, can't shrink but return adjusted size
		return (Slice_Mem){old_allocation.ptr, requested_size};
	}
	U8 aligned_original = align_pow2(old_allocation.len, MEMORY_ALIGNMENT_DEFAULT);
	U8 aligned_new      = align_pow2(requested_size, alignment ? alignment : MEMORY_ALIGNMENT_DEFAULT);
	arena->used    -= (aligned_original - aligned_new);
	return (Slice_Mem){old_allocation.ptr, requested_size};
}
finline void farena_reset(FArena_R arena) { arena->used = 0; }
finline
void farena_rewind(FArena_R arena, AllocatorSP save_point) {
	assert(save_point.type_sig == & farena_allocator_proc);
	U8 end       = arena->start + arena->used; assert_bounds(save_point.slot, arena->start, end);
	arena->used -= save_point.slot - arena->start;
}
finline
AllocatorSP farena_save (FArena arena) {
	return (AllocatorSP){ .type_sig = & farena_allocator_proc, .slot = arena.used };
}
void farena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out*R_ out)
{
	assert(out     != nullptr);
	assert(in.data != null);
	FArena_R arena = cast(FArena_R, in.data);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation = farena_push_mem(arena, in.requested_size, .alignment = in.alignment);
			mem_zero(out->allocation.ptr, out->allocation.len * in.op);
		break;

		case AllocatorOp_Free:                       break;
		case AllocatorOp_Reset: farena_reset(arena); break;

		case AllocatorOp_Grow:
		case AllocatorOp_Grow_NoZero: 
			out->allocation = farena__grow(arena, in.old_allocation, in.requested_size, in.alignment, in.op - AllocatorOp_Grow_NoZero);
		break;
		case AllocatorOp_Shrink:
			out->allocation = farena__shrink(arena, in.old_allocation, in.requested_size, in.alignment);
		break;

		case AllocatorOp_Rewind:    farena_rewind(arena, in.save_point);     break;
		case AllocatorOp_SavePoint: out->save_point = farena_save(arena[0]); break;

		case AllocatorOp_Query:
			out->features =
			  AllocatorQuery_Alloc
			| AllocatorQuery_Reset
			| AllocatorQuery_Resize
			| AllocatorQuery_Rewind
			;
			out->max_alloc  = arena->capacity - arena->used;
			out->min_alloc  = 0;
			out->left       = out->max_alloc;
			out->save_point = farena_save(arena[0]);
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
#define MS_INVALID_HANDLE_VALUE            ((MS_HANDLE)(S8)-1)
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
typedef S8               MS_LONGLONG;
typedef char const*      MS_LPCSTR;
typedef unsigned short*  MS_LPWSTR, *MS_PWSTR;
typedef void*            MS_LPVOID;
typedef MS_DWORD*        MS_LPDWORD;
typedef U8               MS_ULONG_PTR, *MS_PULONG_PTR;
typedef void const*      MS_LPCVOID;
typedef struct MS_SECURITY_ATTRIBUTES *MS_PSECURITY_ATTRIBUTES, *MS_LPSECURITY_ATTRIBUTES;
typedef struct MS_OVERLAPPED          *MS_LPOVERLAPPED;
typedef def_union(MS_LARGE_INTEGER)        { struct { MS_DWORD LowPart; MS_LONG HighPart; } _; struct { MS_DWORD LowPart; MS_LONG HighPart; } u; MS_LONGLONG QuadPart; };
typedef def_struct(MS_FILE)                { void* _Placeholder; };
typedef def_struct(MS_SECURITY_ATTRIBUTES) { MS_DWORD  nLength; A4_B1 _PAD_; MS_LPVOID lpSecurityDescriptor; MS_BOOL bInheritHandle; };
typedef def_struct(MS_OVERLAPPED)          { MS_ULONG_PTR Internal; MS_ULONG_PTR InternalHigh; union { struct { MS_DWORD Offset; MS_DWORD OffsetHigh; } _; void* Pointer; } _; MS_HANDLE  hEvent; };
typedef struct MS_LUID*                    MS_PLUID;
typedef struct MS_LUID_AND_ATTRIBUTES*     MS_PLUID_AND_ATTRIBUTES;
typedef struct MS_TOKEN_PRIVILEGES*        MS_PTOKEN_PRIVILEGES;
typedef def_struct(MS_LUID)                { MS_DWORD LowPart;        MS_LONG HighPart; };
typedef def_struct(MS_LUID_AND_ATTRIBUTES) { MS_LUID  Luid;           MS_DWORD Attributes; };
typedef def_struct(MS_TOKEN_PRIVILEGES)    { MS_DWORD PrivilegeCount; MS_LUID_AND_ATTRIBUTES Privileges[MS_ANYSIZE_ARRAY]; };
W_ MS_BOOL   CloseHandle(MS_HANDLE hObject);
W_ MS_BOOL   AdjustTokenPrivileges(MS_HANDLE TokenHandle, MS_BOOL DisableAllPrivileges, MS_PTOKEN_PRIVILEGES NewState, MS_DWORD BufferLength, MS_PTOKEN_PRIVILEGES PreviousState, MS_PDWORD ReturnLength);
W_ MS_HANDLE GetCurrentProcess(void);
W_ U8        GetLargePageMinimum(void);
W_ MS_BOOL   LookupPrivilegeValueW(MS_LPWSTR lpSystemName, MS_LPWSTR lpName, MS_PLUID lpLuid);
W_ MS_BOOL   OpenProcessToken(MS_HANDLE ProcessHandle, MS_DWORD DesiredAccess, MS_PHANDLE TokenHandle);
W_ MS_LPVOID VirtualAlloc(MS_LPVOID lpAddress, U8 dwSize, MS_DWORD flAllocationType, MS_DWORD flProtect);
W_ MS_BOOL   VirtualFree (MS_LPVOID lpAddress, U8 dwSize, MS_DWORD dwFreeType);
#pragma warning(pop)

typedef def_struct(OS_Windows_State) { OS_SystemInfo system_info; };
global OS_Windows_State os__windows_info;

finline OS_SystemInfo* os_system_info(void) { return & os__windows_info.system_info; }
inline
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
			AdjustTokenPrivileges(token, 0, & priv, size_of(priv), 0, 0);
		}
		CloseHandle(token);
	}
}
inline
void os_init(void) {
	os__enable_large_pages();
	OS_SystemInfo*R_ info = & os__windows_info.system_info;
	info->target_page_size = (U8)GetLargePageMinimum();
}
// TODO(Ed): Large pages disabled for now... (not failing gracefully)
finline U8 os__vmem_reserve(U8 size, Opts_vmem*R_ opts) {
	assert(opts != nullptr);
	void*R_ result = VirtualAlloc(cast(void*R_, opts->base_addr), size
		,	MS_MEM_RESERVE
		// |MS_MEM_COMMIT|(opts->no_large_pages == false ? MS_MEM_LARGE_PAGES : 0)
		,	MS_PAGE_READWRITE
	);
	return u8_(result);
}
finline B4 os__vmem_commit(U8 vm, U8 size, Opts_vmem*R_ opts) {
	assert(opts != nullptr);
	// if (opts->no_large_pages == false ) { return 1; }
	B4 result = (VirtualAlloc(cast(MS_LPVOID, vm), size, MS_MEM_COMMIT, MS_PAGE_READWRITE) != 0);
	return result;
}
inline void  os_vmem_release(U8 vm, U8 size) { VirtualFree(cast(MS_LPVOID, vm), 0, MS_MEM_RESERVE); }
#pragma endregion OS

#pragma region VArena (Virutal Address Space Arena)
finline U8 varena_header_size(void) { return align_pow2(size_of(VArena), MEMORY_ALIGNMENT_DEFAULT); }

inline
VArena* varena__make(Opts_varena_make*R_ opts) {
	assert(opts != nullptr);
	if (opts->reserve_size == 0) { opts->reserve_size = mega(64); }
	if (opts->commit_size  == 0) { opts->commit_size  = mega(64); }
	U8 reserve_size   = align_pow2(opts->reserve_size, os_system_info()->target_page_size);
	U8 commit_size    = align_pow2(opts->commit_size,  os_system_info()->target_page_size);
	B4 no_large_pages = (opts->flags & VArenaFlag_NoLargePages) != 0;
	U8 base           = os_vmem_reserve(reserve_size, .base_addr = opts->base_addr, .no_large_pages = no_large_pages); 
	assert(base != 0);
	os_vmem_commit(base, commit_size, .no_large_pages = no_large_pages);
	U8 header_size = varena_header_size();
	VArena* vm = cast(VArena*, base); r_(vm)[0] = (VArena){
		.reserve_start = base + header_size,
		.reserve       = reserve_size,
		.commit_size   = commit_size,
		.committed     = commit_size,
		.commit_used   = header_size,
		.flags         = opts->flags
	};
	return vm;
}
inline
Slice_Mem varena__push(VArena_R vm, U8 amount, U8 type_width, Opts_varena*R_ opts) {
	assert(vm     != nullptr);
	assert(amount != 0);
	U8 alignment      = opts->alignment ? opts->alignment : MEMORY_ALIGNMENT_DEFAULT;
	U8 requested_size = amount * type_width;
	U8 aligned_size   = align_pow2(requested_size, alignment);
	U8 current_offset = vm->reserve_start + vm->commit_used;
	U8 to_be_used     = vm->commit_used   + aligned_size;
	U8 reserve_left   = vm->reserve       - vm->commit_used;
	U8 commit_left    = vm->committed     - vm->commit_used;
	B4 exhausted      = commit_left < to_be_used; assert(to_be_used < reserve_left);
	if (exhausted)
	{
		U8 next_commit_size = reserve_left > 0 ?
			max(vm->commit_size, to_be_used)
		:	align_pow2( reserve_left, os_system_info()->target_page_size);
		if (next_commit_size) {
			U8 next_commit_start = u8_(vm) + vm->committed;
			B4 no_large_pages    = (vm->flags & VArenaFlag_NoLargePages) != 0;
			B4 commit_result     = os_vmem_commit(next_commit_start, next_commit_size, .no_large_pages = no_large_pages);
			if (commit_result == false) { return (Slice_Mem){0}; }
			vm->committed += next_commit_size;
		}
	}
	vm->commit_used = to_be_used;
	return (Slice_Mem){.ptr = current_offset, .len = requested_size};
}
inline
Slice_Mem varena__grow(VArena_R vm, Slice_Mem old_allocation, U8 requested_size, U8 alignment, B4 no_zero) {
	U8 grow_amount = requested_size - old_allocation.len;
	if (grow_amount == 0) { return old_allocation; }                    // Growing when not the last allocation not allowed
	U8 current_offset = vm->reserve_start + vm->commit_used;            assert(old_allocation.ptr == current_offset); 
	Slice_Mem allocation = varena_push_mem(vm, grow_amount, alignment); assert(allocation.ptr != 0);
	Slice_Mem result     = (Slice_Mem){ old_allocation.ptr, requested_size + allocation.len }; 
	mem_zero(result.ptr, result.len * no_zero);
	return result;
}
finline void varena_release(VArena_R arena) { os_vmem_release(u8_(arena), arena->reserve); }
inline
Slice_Mem varena__shrink(VArena_R vm, Slice_Mem old_allocation, U8 requested_size) {
	U8 shrink_amount = old_allocation.len - requested_size;
	if (lt_s(shrink_amount, 0)) { return old_allocation; }
	U8 current_offset = vm->reserve_start + vm->commit_used; assert(old_allocation.ptr == current_offset);
	vm->commit_used  -= shrink_amount;
	return (Slice_Mem){ old_allocation.ptr, requested_size };
}
finline
void varena_rewind(VArena_R vm, AllocatorSP sp) {
	assert(vm != nullptr);
	assert(sp.type_sig == & varena_allocator_proc);
	vm->commit_used = max(sp.slot, sizeof(VArena));
}
finline AllocatorSP varena_save(VArena_R vm) { return (AllocatorSP){varena_allocator_proc, vm->commit_used}; }
void varena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out* out)
{
	VArena_R vm = cast(VArena_R, in.data);
	switch (in.op)
	{
		case AllocatorOp_Alloc:
		case AllocatorOp_Alloc_NoZero:
			out->allocation = varena_push_mem(vm, in.requested_size, .alignment = in.alignment);
			mem_zero(out->allocation.ptr, out->allocation.len * in.op);
		break;

		case AllocatorOp_Free:                       break; 
		case AllocatorOp_Reset: vm->commit_used = 0; break;

		case AllocatorOp_Grow_NoZero:
		case AllocatorOp_Grow:
			out->allocation = varena__grow(vm, in.old_allocation, in.requested_size, in.alignment, in.op - AllocatorOp_Grow_NoZero);
		break;
		case AllocatorOp_Shrink:
			out->allocation = varena__shrink(vm, in.old_allocation, in.requested_size);
		break;

		case AllocatorOp_Rewind:    vm->commit_used = in.save_point.slot; break;
		case AllocatorOp_SavePoint: out->save_point = varena_save(vm);    break;

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

#pragma region Arena (Chained Arena)
inline
Arena* arena__make(Opts_arena_make*R_ opts) {
	assert(opts != nullptr);
	U8 header_size  = align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT);
	VArena_R current = varena__make(opts);
	assert(current != nullptr);
	Arena* arena = varena_push(current, Arena); r_(arena)[0] = (Arena){
		.backing  = current,
		.prev     = nullptr,
		.current  = arena,
		.base_pos = 0,
		.pos      = header_size,
		.flags    = opts->flags,
	};
	return arena;
}
Slice_Mem arena__push(Arena_R arena, U8 amount, U8 type_width, Opts_arena* opts) {
	assert(arena != nullptr);
	assert(opts  != nullptr);
	Arena_R active    = arena->current;
	U8 size_requested = amount * type_width;
	U8 alignment      = opts->alignment ? opts->alignment : MEMORY_ALIGNMENT_DEFAULT;
	U8 size_aligned   = align_pow2(size_requested, alignment);
	U8 pos_pre        = active->pos;
	U8 pos_pst        = pos_pre + size_aligned;
	B4 should_chain =
		((arena->flags & ArenaFlag_NoChain) == 0)
	&&	active->backing->reserve < pos_pst;
	if (should_chain)
	{
		Arena_R new_arena = arena_make(
			.base_addr    = 0,
			.reserve_size = active->backing->reserve,
			.commit_size  = active->backing->commit_size,
			.flags        = active->backing->flags,
		);
		new_arena->base_pos = active->base_pos + active->backing->reserve;
		sll_stack_push_n(arena->current, new_arena, prev);
		active = arena->current;
	}
	U8         result = u8_(active) + pos_pre;
	Slice_Mem vresult = varena_push_mem(active->backing, size_aligned, .alignment = alignment);
	slice_assert(vresult);
	assert(result == vresult.ptr);
	active->pos = pos_pst;
	return vresult;
}
finline
void arena_release(Arena_R arena) {
	assert(arena != nullptr);
	Arena_R curr = arena->current;
	Arena_R prev = nullptr;
	for (; curr != nullptr;	curr = prev) {
		prev = curr->prev;
		varena_release(curr->backing);
	}
}
finline void arena_reset(Arena_R arena) { arena_rewind(arena, (AllocatorSP){.type_sig = arena_allocator_proc, .slot = 0}); }
void arena_rewind(Arena_R arena, AllocatorSP save_point) {
	assert(arena != nullptr);
	assert(save_point.type_sig == arena_allocator_proc);
	U8      header_size = align_pow2(size_of(Arena), MEMORY_ALIGNMENT_DEFAULT);
	Arena_R curr        = arena->current;
	U8      big_pos     = clamp_bot(header_size, save_point.slot);
	for (Arena_R prev = nullptr; curr->base_pos >= big_pos; curr = prev) {
		prev = curr->prev;
		varena_release(curr->backing);
	}
	arena->current = curr;
	U8 new_pos = big_pos - curr->base_pos;
	assert(new_pos <= curr->pos);
	curr->pos = new_pos;
	varena_rewind(curr->backing, (AllocatorSP){varena_allocator_proc, curr->pos + size_of(VArena)});
}
finline AllocatorSP arena_save(Arena_R arena) { return (AllocatorSP){arena_allocator_proc, arena->base_pos + arena->current->pos}; }
void arena_allocator_proc(AllocatorProc_In in, AllocatorProc_Out*R_ out)
{
	assert(out != nullptr);
	Arena_R arena = cast(Arena_R, in.data);
	assert(arena != nullptr);
	switch (in.op)
	{
	case AllocatorOp_Alloc:
	case AllocatorOp_Alloc_NoZero:
		out->allocation = arena_push_mem(arena, in.requested_size, .alignment = in.alignment);
		mem_zero(out->allocation.ptr, out->allocation.len * in.op);
	break;

	case AllocatorOp_Free:                      break;
	case AllocatorOp_Reset: arena_reset(arena); break;

	case AllocatorOp_Grow:
	case AllocatorOp_Grow_NoZero: {
		Arena_R active = arena->current;
		U8 alloc_end = in.old_allocation.ptr + in.old_allocation.len;
		U8 arena_end = u8_(active) + active->pos;
		if (alloc_end == arena_end)
		{
			U8 grow_amount  = in.requested_size - in.old_allocation.len;
			U8 aligned_grow = align_pow2(grow_amount, in.alignment ? in.alignment : MEMORY_ALIGNMENT_DEFAULT);
			if (active->pos + aligned_grow <= active->backing->reserve)
			{
				Slice_Mem vresult = varena_push_mem(active->backing, aligned_grow, .alignment = in.alignment);
				if (vresult.ptr != null)
				{
					active->pos          += aligned_grow;
					out->allocation       = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
					mem_zero(in.old_allocation.ptr + in.old_allocation.len, grow_amount * in.op - AllocatorOp_Grow_NoZero);
					break;
				}
			}
		}
		Slice_Mem new_alloc = arena__push(arena, in.requested_size, 1, &(Opts_arena){.alignment = in.alignment});
		if (new_alloc.ptr == null) {
			out->allocation = (Slice_Mem){0};
			break;
		}
		mem_copy(new_alloc.ptr, in.old_allocation.ptr, in.old_allocation.len);
		mem_zero(new_alloc.ptr + in.old_allocation.len, (in.requested_size - in.old_allocation.len) * in.op - AllocatorOp_Grow_NoZero);
		out->allocation       = new_alloc;
	}
	break;

	case AllocatorOp_Shrink: {
		Arena_R active = arena->current;
		U8 alloc_end = in.old_allocation.ptr + in.old_allocation.len;
		U8 arena_end = u8_(active) + active->pos;
		if (alloc_end != arena_end) {
			out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
			break;
		}
		//SSIZE shrink_amount    = in.old_allocation.len - in.requested_size;
		U8 aligned_original = align_pow2(in.old_allocation.len, MEMORY_ALIGNMENT_DEFAULT);
		U8 aligned_new      = align_pow2(in.requested_size, in.alignment ? in.alignment : MEMORY_ALIGNMENT_DEFAULT);
		U8 pos_reduction    = aligned_original - aligned_new;
		active->pos        -= pos_reduction;
		varena__shrink(active->backing, in.old_allocation, in.requested_size);
		out->allocation = (Slice_Mem){in.old_allocation.ptr, in.requested_size};
	}
	break;

	case AllocatorOp_Rewind:    arena_rewind(arena, in.save_point);  break;
	case AllocatorOp_SavePoint: out->save_point = arena_save(arena); break;

	case AllocatorOp_Query:
		out->features =
			AllocatorQuery_Alloc
		|	AllocatorQuery_Resize
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

#pragma region Key Table Linear (KTL)
inline
void ktl_populate_slice_a2_str8(KTL_Str8*R_ kt, AllocatorInfo backing, Slice_A2_Str8 values) {
	assert(kt != nullptr);
	if (values.len == 0) return;
	* kt = alloc_slice(backing, KTL_Slot_Str8, values.len);
	for span_iter(U8, id, 0, <, values.len) { 
		mem_copy(u8_(& kt->ptr[id.cursor].value), u8_(& values.ptr[id.cursor][1]), size_of(Str8));
		hash64_fnv1a(& kt->ptr[id.cursor].key, slice_mem_s(values.ptr[id.cursor][0]));
	}
}
#pragma endregion KTL

#pragma region Key Table 1-Layer Chained-Chunked_Cells (KT1CX)
inline
void kt1cx_init(KT1CX_Info info, KT1CX_InfoMeta m, KT1CX_Byte*R_ result) {
	assert(result                  != nullptr);
	assert(info.backing_cells.proc != nullptr);
	assert(info.backing_table.proc != nullptr);
	assert(m.cell_depth     >  0);
	assert(m.cell_pool_size >= kilo(4));
	assert(m.table_size     >= kilo(4));
	assert(m.type_width     >  0);
	result->table     = mem_alloc(info.backing_table, m.table_size * m.cell_size); slice_assert(result->table);
	result->table.len = m.table_size; // Setting to the table number of elements instead of byte length.
}
inline
void kt1cx_clear(KT1CX_Byte kt, KT1CX_ByteMeta m) {
	U8 cell_cursor = kt.table.ptr;
	U8 table_len   = kt.table.len * m.cell_size;
	for (; cell_cursor != slice_end(kt.table); cell_cursor += m.cell_size ) // for cell in kt.table.cells
	{
		Slice_Mem slots       = {cell_cursor, m.cell_depth * m.slot_size }; // slots = cell.slots
		U8        slot_cursor = slots.ptr;
		for (; slot_cursor < slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			Slice_Mem slot = {slot_cursor, m.slot_size}; // slot = slots[id]
			mem_zero(slot.ptr, slot.len);                // clear(slot)
		}
		U8 next = slot_cursor + m.cell_next_offset; // next = slots + next_cell_offset
		if (next != null) {
			slots.ptr   = next; // slots = next
			slot_cursor = next;
			goto process_slots;
		}
	}
}
finline
U8 kt1cx_slot_id(KT1CX_Byte kt, U8 key, KT1CX_ByteMeta m) {
	U8 hash_index = key % kt.table.len;
	return hash_index;
}
U8 kt1cx_get(KT1CX_Byte kt, U8 key, KT1CX_ByteMeta m) {
	U8 hash_index  = kt1cx_slot_id(kt, key, m);
	U8 cell_offset = hash_index * m.cell_size;
	U8 cell_cursor = kt.table.ptr + cell_offset; // KT1CX_Cell_<Type> cell = kt.table[hash_index]
	{
		Slice_Mem slots       = {cell_cursor, m.cell_depth * m.slot_size}; // KT1CX_Slot_<Type>[kt.cell_depth] slots = cell.slots
		U8        slot_cursor = slots.ptr;
		for (; slot_cursor != slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			KT1CX_Byte_Slot_R slot = cast(KT1CX_Byte_Slot_R, slot_cursor + m.slot_key_offset); // slot = slots[id]     KT1CX_Slot_<Type>
			if (slot->occupied && slot->key == key) {
				return slot_cursor;
			}
		}
		U8 cell_next = cell_cursor + m.cell_next_offset; // cell.next
		if (cell_next != null) {
			slots.ptr   = cell_next; // slots = cell_next
			slot_cursor = cell_next;
			cell_cursor = cell_next; // cell = cell_next
			goto process_slots;
		}
		else {
			return null;
		}
	}
}
inline
U8 kt1cx_set(KT1CX_Byte kt, U8 key, Slice_Mem value, AllocatorInfo backing_cells, KT1CX_ByteMeta m) {
	U8 hash_index  = kt1cx_slot_id(kt, key, m);
	U8 cell_offset = hash_index * m.cell_size;
	U8 cell_cursor = kt.table.ptr + cell_offset; // KT1CX_Cell_<Type> cell = kt.table[hash_index]
	// U8 cell_cursor = u1_rkt.table.ptr + cell_offset; // KT1CX_Cell_<Type> cell = kt.table[hash_index]
	{
		Slice_Mem slots       = {cell_cursor, m.cell_depth * m.slot_size}; // cell.slots
		U8        slot_cursor = slots.ptr;
		for (; slot_cursor != slice_end(slots); slot_cursor += m.slot_size) {
		process_slots:
			KT1CX_Byte_Slot_R slot = cast(KT1CX_Byte_Slot_R, slot_cursor + m.slot_key_offset);
			if (slot->occupied == false) {
				slot->occupied = true;
				slot->key      = key;
				return slot_cursor;
			}
			else if (slot->key == key) {
				return slot_cursor;
			}
		}
		KT1CX_Byte_Cell curr_cell = { cell_cursor + m.cell_next_offset }; // curr_cell = cell
		if ( curr_cell.next != null) {
			slots.ptr   = curr_cell.next;
			slot_cursor = curr_cell.next;
			cell_cursor = curr_cell.next;
			goto process_slots;
		}
		else {
			Slice_Mem new_cell = mem_alloc(backing_cells, m.cell_size);
			curr_cell.next     = new_cell.ptr;
			KT1CX_Byte_Slot_R slot = cast(KT1CX_Byte_Slot_R, new_cell.ptr + m.slot_key_offset);
			slot->occupied = true;
			slot->key      = key;
			return new_cell.ptr;
		}
	}
	assert_msg(false, "impossible path");
	return null;
}
#pragma endregion Key Table

#pragma region String Operations
finline
char* str8_to_cstr_capped(Str8 content, Slice_Mem mem) {
	U8 copy_len = min(content.len, mem.len - 1);
	mem_copy(mem.ptr, u8_(content.ptr), copy_len);
	u1_r(mem.ptr)[copy_len] = '\0';
	return cast(char*, mem.ptr);
}
Str8 str8_from_u32(AllocatorInfo ainfo, U4 num, U4 radix, U4 min_digits, U4 digit_group_separator)
{
	Str8 result = {0};
	Str8 prefix = {0};
	switch (radix) {
		case 16: { prefix = lit("0x"); } break;
		case 8:  { prefix = lit("0o"); } break;
		case 2:  { prefix = lit("0b"); } break;
	}
	U4 digit_group_size = 3;
	switch (radix) {
		default: break;
		case 2:
		case 8:
		case 16: {
			digit_group_size = 4;
		}
		break;
	}
	U4 needed_leading_zeros = 0;
	{
		U4 needed_digits = 1;
		{
			U4 u32_reduce = num;
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
		U4 needed_separators    = 0;
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
		U4 num_reduce             = num;
		U4 digits_until_separator = digit_group_size;
		for (U8 idx = 0; idx < result.len; idx += 1)
		{
			U8 separator_pos = result.len - idx - 1;
			if (digits_until_separator == 0 && digit_group_separator != 0) {
				result.ptr[separator_pos] = u1_(digit_group_separator);
				digits_until_separator = digit_group_size + 1;
			}
			else {
				result.ptr[separator_pos] = (U1) char_to_lower(integer_symbols(u1_(num_reduce % radix)));
				num_reduce /= radix;
			}
			digits_until_separator -= 1;
			if (num_reduce == 0) {
				break;
			}
		}
		for (U8 leading_0_idx = 0; leading_0_idx < needed_leading_zeros; leading_0_idx += 1) {
			result.ptr[prefix.len + leading_0_idx] = '0';
		}
	}
	// Fill Prefix
	if (prefix.len > 0) {
		slice_copy(result, prefix);
	}
	return result;
}
internal
Str8 str8__fmt_ktl(AllocatorInfo ainfo, Slice_Mem*R_ _buffer, KTL_Str8 table, Str8 fmt_template)
{
	assert(_buffer != nullptr);
	Slice_Mem buffer = _buffer[0];
	slice_assert(buffer);
	slice_assert(table);
	slice_assert(fmt_template);
	assert(ainfo.proc != nullptr ? (allocator_query(ainfo).features & AllocatorQuery_Grow) != 0 : true);
	UTF8_R cursor_buffer    = cast(UTF8_R, buffer.ptr);
	U8     buffer_remaining = buffer.len;

	UTF8_R cursor_fmt = fmt_template.ptr;
	U8     left_fmt   = fmt_template.len;
	while (left_fmt && buffer_remaining)
	{
		// Forward until we hit the delimiter '<' or the template's contents are exhausted.
		U8 copy_offset = 0;
		while (cursor_fmt[copy_offset] != '<' && (cursor_fmt + copy_offset) < slice_end(fmt_template)) {
			++ copy_offset;
		}
		mem_copy(u8_(cursor_buffer), u8_(cursor_fmt), copy_offset);
		buffer_remaining -= copy_offset;
		left_fmt         -= copy_offset;
		cursor_buffer    += copy_offset;
		cursor_fmt       += copy_offset;

		if (cursor_fmt[0] == '<')
		{
			UTF8_R potential_token_cursor = cursor_fmt + 1;
			U8     potential_token_len    = 0;
			B4     fmt_overflow           = false;
			for (;;) {
				UTF8_R cursor       = potential_token_cursor + potential_token_len;
				fmt_overflow        = cursor >= slice_end(fmt_template);
				B4 found_terminator = potential_token_cursor[potential_token_len] == '>';
				if (fmt_overflow || found_terminator) { break; }
				++ potential_token_len;
			}
			if (fmt_overflow) continue;
			// Hashing the potential token and cross checking it with our token table
			U8     key   = 0; 
			hash64_fnv1a(& key, slice_mem(u8_(potential_token_cursor), potential_token_len));
			Str8_R value = nullptr;
			for slice_iter(table, token) {
				// We do a linear iteration instead of a hash table lookup because the user should be never substiuting with more than 100 unqiue tokens..
				if (token->key == key) {
					value = & token->value;
					break;
				}
			}
			if (value)
			{
				// We're going to appending the string, make sure we have enough space in our buffer.
				if (ainfo.proc != nullptr && (buffer_remaining - potential_token_len) <= 0) {
					buffer            = mem_grow(ainfo, buffer, buffer.len + potential_token_len);
					buffer_remaining += potential_token_len;
				}
				assert((buffer_remaining - potential_token_len) > 0);
				mem_copy(u8_(cursor_buffer), u8_(value->ptr), value->len);
				// Sync cursor format to after the processed token
				cursor_buffer    += value->len;
				buffer_remaining -= value->len;
				cursor_fmt        = potential_token_cursor + potential_token_len + 1;
				left_fmt         -= potential_token_len + 2; // The 2 here are the '<' & '>' delimiters being omitted.
				continue;
			}
			// If not a subsitution, we do a single copy for the '<' and continue.
			cursor_buffer[0] = cursor_fmt[0];
			++ cursor_buffer;
			++ cursor_fmt;
			-- buffer_remaining;
			-- left_fmt;
			continue;
		}
	}
	_buffer[0] = buffer;
	Str8   result = {cast(UTF8_R, buffer.ptr), buffer.len - buffer_remaining};
	return result;
}
finline
Str8 str8__fmt_backed(AllocatorInfo tbl_backing, AllocatorInfo buf_backing, Str8 fmt_template, Slice_A2_Str8*R_ entries) {
	KTL_Str8 kt; kt1l_populate_slice_a2_str8(& kt, tbl_backing, entries[0] );
	U8 buf_size = kilo(64); Slice_Mem buffer = mem_alloc(buf_backing, buf_size);
	Str8   result = str8__fmt_ktl(buf_backing, & buffer, kt, fmt_template);
	return result;
}
Str8 str8__fmt(Str8 fmt_template, Slice_A2_Str8*R_ entries) {
	local_persist B1 tbl_mem[kilo(32)];  FArena tbl_arena = farena_make(slice_fmem(tbl_mem));
	local_persist B1 buf_mem[kilo(64)];
	KTL_Str8 kt = {0}; ktl_populate_slice_a2_str8(& kt, ainfo_farena(tbl_arena), entries[0] );
	Str8   result = str8__fmt_ktl((AllocatorInfo){0}, & slice_fmem(buf_mem), kt, fmt_template);
	return result;
}
inline
void str8cache__init(Str8Cache_R cache, Opts_str8cache_init*R_ opts) {
	assert(cache != nullptr);
	assert(opts  != nullptr);
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
	};
	KT1CX_InfoMeta m = {
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
	kt1cx_init(info, m, cast(KT1CX_Byte*R_, & cache->kt));
	return;
}
finline Str8Cache str8cache__make(Opts_str8cache_init*R_ opts) { Str8Cache cache; str8cache__init(& cache, opts); return cache; }
finline
void str8cache_clear(KT1CX_Str8 kt) {
	kt1cx_assert(kt);
	kt1cx_clear(kt1cx_byte(kt),
	(KT1CX_ByteMeta){
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	});
}
finline
Str8* str8cache_get(KT1CX_Str8 kt, U8 key) {
	kt1cx_assert(kt);
	U8 result = kt1cx_get(kt1cx_byte(kt), key
	,	(KT1CX_ByteMeta){
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	});
	return cast(Str8*, result);
}
finline
Str8* str8cache_set(KT1CX_Str8 kt, U8 key, Str8 value, AllocatorInfo str_reserve, AllocatorInfo backing_cells) {
	kt1cx_assert(kt);
	slice_assert(value);
	assert(str_reserve.proc != nullptr);
	assert(backing_cells.proc != nullptr);
	U8 entry = kt1cx_set(kt1cx_byte(kt), key, slice_mem_s(value), backing_cells, (KT1CX_ByteMeta){
		.slot_size        = size_of(KT1CX_Slot_Str8),
		.slot_key_offset  = offset_of(KT1CX_Slot_Str8, key),
		.cell_next_offset = offset_of(KT1CX_Cell_Str8, next),
		.cell_depth       = Str8Cache_CELL_DEPTH,
		.cell_size        = size_of(KT1CX_Cell_Str8),
		.type_width       = size_of(Str8),
		.type_name        = lit(stringify(Str8))
	});
	assert(entry != null);
	Str8* result = pcast(Str8*, entry);
	B4  is_empty = (result->len == 0);
	if (is_empty) {
		result[0] = alloc_slice(str_reserve, UTF8, value.len);
		slice_copy(result[0], value);
	}
	return result;
}
finline
Str8 cache_str8(Str8Cache_R cache, Str8 str) {
	assert(cache != nullptr);
	U8     key    = 0; hash64_fnv1a(& key, slice_mem_s(str));
	Str8_R result = str8cache_set(cache->kt, key, str, cache->str_reserve, cache->cell_reserve);
	return result[0];
}
finline
void str8gen_init(Str8Gen_R gen, AllocatorInfo backing) {
	assert(gen != nullptr);
	gen->backing = backing;
	gen->ptr = cast(UTF8_R, mem_alloc(backing, kilo(4)).ptr);
	assert(gen->ptr != null);
	gen->len = 0;
	gen->cap = kilo(4);
}
finline Str8Gen str8gen_make(AllocatorInfo backing) { Str8Gen gen; str8gen_init(& gen, backing); return gen; }
finline
void str8gen_append_str8(Str8Gen_R gen, Str8 str){
	Slice_Mem result = mem_grow(gen->backing, str8gen_slice_mem(gen[0]), str.len + gen->len);
	slice_assert(result);
	Slice_B1 to_copy = { cast(B1_R, result.ptr + gen->len), result.len - gen->len };
	slice_copy(to_copy, slice_to_bytes(str));
	gen->ptr  = cast(UTF8_R, result.ptr); 
	gen->len += str.len;
	gen->cap  = result.len;
}
void str8gen__append_fmt(Str8Gen_R gen, Str8 fmt_template, Slice_A2_Str8*R_ entries){
	local_persist B1 tbl_mem[kilo(32)]; FArena tbl_arena = farena_make(slice_fmem(tbl_mem));
	KTL_Str8 kt     = {0}; ktl_populate_slice_a2_str8(& kt, ainfo_farena(tbl_arena), entries[0] );
	Slice_Mem buffer = { cast(U8, gen->ptr) + gen->len, gen->cap - gen->len };
	if (buffer.len < kilo(16)) {
		Slice_Mem result = mem_grow(gen->backing, str8gen_slice_mem(gen[0]), kilo(16) + gen->cap );
		slice_assert(result);
		gen->ptr  = cast(UTF8_R, result.ptr);
		gen->cap += kilo(16);
		buffer    = (Slice_Mem){ cast(U8, gen->ptr) + gen->len, gen->cap - gen->len };
	}
	Str8 result = str8__fmt_ktl(gen->backing, & buffer, kt, fmt_template);
	gen->len   += result.len;
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
W_ MS_HANDLE CreateFileA(
	MS_LPCSTR                lpFileName,
	MS_DWORD                 dwDesiredAccess,
	MS_DWORD                 dwShareMode,
	MS_LPSECURITY_ATTRIBUTES lpSecurityAttributes,
	MS_DWORD                 dwCreationDisposition,
	MS_DWORD                 dwFlagsAndAttributes,
	MS_HANDLE                hTemplateFile);
W_ MS_BOOL ReadFile(
	MS_HANDLE       hFile,
	MS_LPVOID       lpBuffer,
	MS_DWORD        nNumberOfBytesToRead,
	MS_LPDWORD      lpNumberOfBytesRead,
	MS_LPOVERLAPPED lpOverlapped);
W_ MS_BOOL WriteFile(
	MS_HANDLE       hFile,
	MS_LPCVOID      lpBuffer,
	MS_DWORD        nNumberOfBytesToWrite,
	MS_LPDWORD      lpNumberOfBytesWritten,
	MS_LPOVERLAPPED lpOverlapped);
W_ MS_BOOL  GetFileSizeEx(MS_HANDLE hFile, MS_LARGE_INTEGER* lpFileSize);
W_ MS_DWORD GetLastError(void);

finline
FileOpInfo file__read_contents(Str8 path, Opts_read_file_contents*R_ opts) {
	assert(opts != nullptr);
	FileOpInfo result = {0}; api_file_read_contents(& result, path, opts[0]);
	return result;
}
void api_file_read_contents(FileOpInfo_R result, Str8 path, Opts_read_file_contents opts)
{
	assert(result != nullptr);
	slice_assert(path);
	// Backing is required at this point
	assert(opts.backing.proc != nullptr);
	// This will limit a path for V1 to be 32kb worth of codepoints.
	local_persist U1 scratch[kilo(64)];
	char const*R_ path_cstr = str8_to_cstr_capped(path, slice_fmem(scratch) );
	MS_HANDLE id_file = CreateFileA(
		path_cstr,
		MS_GENERIC_READ,
		MS_FILE_SHARE_READ,
		nullptr,
		MS_OPEN_EXISTING,
		MS_FILE_ATTRIBUTE_NORMAL,
		nullptr
	);
	B4 open_failed = id_file == MS_INVALID_HANDLE_VALUE;
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
	Slice_Mem buffer = mem_alloc(opts.backing, u8_(file_size.QuadPart));
	B4 not_enough_backing = s8_(buffer.len) < file_size.QuadPart;
	if (not_enough_backing) {
		assert(not_enough_backing);
		result->content = (Slice_Mem){0};
		return;
	}
	if (opts.zero_backing) {
		mem_zero(buffer.ptr, buffer.len);
	}
	MS_DWORD amount_read = 0;
	MS_BOOL  read_result = ReadFile(
		id_file,
		cast(MS_LPVOID, buffer.ptr),
		cast(MS_DWORD, file_size.QuadPart),
		& amount_read,
		nullptr
	);
	CloseHandle(id_file);
	B4 read_failed  = ! read_result;
	   read_failed |= amount_read != file_size.QuadPart;
	if (read_failed) {
		assert(read_failed);
		return;
	}
	result->content.ptr = buffer.ptr;
	result->content.len = u8_(file_size.QuadPart);
	return;
}
void file_write_str8(Str8 path, Str8 content)
{
	slice_assert(path);
	local_persist U1 scratch[kilo(64)] = {0};
	char const*R_ path_cstr = str8_to_cstr_capped(path, slice_fmem(scratch));
	MS_HANDLE id_file = CreateFileA(
		path_cstr,
		MS_GENERIC_WRITE,
		MS_FILE_SHARE_READ,
		nullptr,
		MS_CREATE_ALWAYS,
		MS_FILE_ATTRIBUTE_NORMAL,
		nullptr
	);
	B4 open_failed = id_file == MS_INVALID_HANDLE_VALUE;
	if (open_failed) {
		MS_DWORD  error_code = GetLastError();
		assert(error_code != 0);
		return;
	}
	MS_DWORD bytes_written = 0;
	MS_BOOL  status = WriteFile(id_file
		, cast(MS_HANDLE, content.ptr)
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
no_inline
U8* __cdecl __local_stdio_printf_options(void) {
	// NOTE(CRT): This function must not be inlined into callers to avoid ODR violations.  The
	// static local variable has different names in C and in C++ translation units.
	local_persist U8 _OptionsStorage; return &_OptionsStorage;
}
int __cdecl __stdio_common_vfprintf_s(
	U8               _Options,
	MS_FILE*         _Stream,
	char const*      _Format,
	_locale_t        _Locale,
	va_list          _ArgList
);
void __cdecl __va_start(va_list* , ...);
finline
int printf_err(char const* fmt, ...) {
	int result;
	va_list args;
	va_start(args, fmt);
	result = __stdio_common_vfprintf_s(MS_CRT_INTERNAL_LOCAL_PRINTF_OPTIONS, MS_stderr, fmt, nullptr, args);
	va_end(args);
	return result;
}
void assert_handler( UTF8*R_ condition, UTF8*R_ file, UTF8*R_ function, S4 line, UTF8*R_ msg, ... ) {
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
void api_watl_lex(WATL_LexInfo_R info, Str8 source, Opts_watl_lex*R_ opts)
{
	if (source.len == 0) { return; }
	assert(info                  != nullptr);
	assert(opts                  != nullptr);
	assert(opts->ainfo_msgs.proc != nullptr);
	assert(opts->ainfo_toks.proc != nullptr);
	WATL_LexMsg_R msg_last = nullptr;

	UTF8_R end    = source.ptr + source.len;
	UTF8_R cursor = source.ptr;
	UTF8_R prev   = cursor - 1;
	UTF8   code   = cursor[0];
	WATL_Tok_R tok            = nullptr;
	U8         num            = 0;
	B4         was_formatting = true;
	for (; cursor < end;)
	{
	#define alloc_tok() alloc_type(opts->ainfo_toks, WATL_Tok, .alignment = alignof(WATL_Tok), .no_zero = true)
		switch (code)
		{
			case WATL_Tok_Space:
			case WATL_Tok_Tab:
			{
				if (prev[0] != cursor[0]) {
					WATL_Tok_R new_tok = alloc_tok(); if (new_tok - 1 != tok && tok != nullptr) { goto slice_constraint_fail; }
					tok            = new_tok;
					tok[0]         = (WATL_Tok){ cursor, 0 };
					was_formatting = true;
					++ num;
				}
				cursor   += 1;
				tok->len += 1;
			}
			break;
			case WATL_Tok_LineFeed: {
				WATL_Tok_R new_tok = alloc_tok(); if (new_tok - 1 != tok && tok != nullptr) { goto slice_constraint_fail; }
				tok            = new_tok;
				tok[0]         = (WATL_Tok){ cursor, 1 };
				cursor        += 1;
				was_formatting = true;
				++ num;
			}
			break;
			// Assuming what comes after is line feed.
			case WATL_Tok_CarriageReturn: {
				WATL_Tok_R new_tok = alloc_tok(); if (new_tok - 1 != tok && tok != nullptr) { goto slice_constraint_fail; }
				tok            = new_tok;
				tok[0]         = (WATL_Tok){ cursor, 2 };
				cursor        += 2;
				was_formatting = true;
				++ num;
			}
			break;
			default:
			{
				if (was_formatting) {
					WATL_Tok_R new_tok = alloc_tok(); if (new_tok - 1 != tok && tok != nullptr) { goto slice_constraint_fail; }
					tok            = new_tok;
					tok[0]         = (WATL_Tok){ cursor, 0 };
					was_formatting = false;
					++ num;
				}
				cursor   += 1;
				tok->len += 1;
			}
			break;
		}
		prev = cursor - 1;
		code = cursor[0];
	#undef alloc_tok
	}
	assert(tok != nullptr);
	assert(num > 0);
	info->toks.ptr = tok - num + 1;
	info->toks.len = num;
	return;
slice_constraint_fail:
	info->signal |= WATL_LexStatus_MemFail_SliceConstraintFail;
	WATL_LexMsg_R msg = alloc_type(opts->ainfo_msgs, WATL_LexMsg);
	assert(msg != nullptr);
	msg->pos     = (WATL_Pos){ -1, -1 };
	msg->tok     = tok;
	msg->content = lit("Token slice allocation was not contiguous");
	sll_queue_push_n(info->msgs, msg_last, msg, next);
	assert(opts->failon_slice_constraint_fail == false);
	return;
}
inline WATL_LexInfo watl__lex(Str8 source, Opts_watl_lex*R_ opts) { WATL_LexInfo info = {0}; api_watl_lex(& info, source, opts); return info; }

void api_watl_parse(WATL_ParseInfo_R info, Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts)
{
	if (tokens.len == 0) { return; }
	assert(opts                   != nullptr);
	assert(opts->ainfo_lines.proc != nullptr);
	assert(opts->ainfo_msgs.proc  != nullptr);
	assert(opts->ainfo_nodes.proc != nullptr);
	assert(opts->str_cache        != nullptr);
	WATL_ParseMsg_R msg_last = nullptr;

	WATL_Line_R line = alloc_type(opts->ainfo_lines, WATL_Line);
	WATL_Node_R curr = alloc_type(opts->ainfo_nodes, WATL_Node);
	curr[0]     = (WATL_Node){0};
	line[0]     = (WATL_Line){ curr, 0 };
	info->lines = (Slice_WATL_Line){ line, 0 };
	for slice_iter(tokens, token)
	{
		switch(token->ptr[0])
		{
			case WATL_Tok_CarriageReturn:
			case WATL_Tok_LineFeed:
			{
				WATL_Line_R new_line = alloc_type(opts->ainfo_lines, WATL_Line); if (new_line - 1 != line) {
					info->signal |= WATL_ParseStatus_MemFail_SliceConstraintFail;
					WATL_ParseMsg_R msg = alloc_type(opts->ainfo_msgs, WATL_ParseMsg);
					msg->content = lit("Line slice allocation was not contiguous");
					msg->pos     = (WATL_Pos){cast(S4, info->lines.len), cast(S4, line->len)};
					msg->line    = line;
					msg->tok     = token;
					sll_queue_push_n(info->msgs, msg_last, msg, next);
					assert(opts->failon_slice_constraint_fail == false);
					return;
				}
				line             = new_line;
				line->ptr        = curr;
				info->lines.len += 1;
			}
			continue;

			default:
			break;
		}
		curr[0] = cache_str8(opts->str_cache, token[0]);
		WATL_Node_R new_node = alloc_type(opts->ainfo_nodes, WATL_Node); if (new_node - 1 != curr) { 
			info->signal |= WATL_ParseStatus_MemFail_SliceConstraintFail;
			WATL_ParseMsg_R msg = alloc_type(opts->ainfo_msgs, WATL_ParseMsg);
			msg->content = lit("Nodes slice allocation was not contiguous");
			msg->pos     = (WATL_Pos){cast(S4, info->lines.len), cast(S4, line->len)};
			msg->line    = line;
			msg->tok     = token;
			sll_queue_push_n(info->msgs, msg_last, msg, next);
			assert(opts->failon_slice_constraint_fail == false);
			return;
		}
		curr       = new_node;
		line->len += 1;
		continue;
	}
	return;
}
inline WATL_ParseInfo watl__parse(Slice_WATL_Tok tokens, Opts_watl_parse*R_ opts) { WATL_ParseInfo info = {0}; api_watl_parse(& info, tokens, opts); return info; }

Str8 watl_dump_listing(AllocatorInfo buffer, Slice_WATL_Line lines)
{
	local_persist B1 scratch[kilo(64)] = {0}; FArena sarena = farena_make(slice_fmem(scratch)); AllocatorInfo sinfo = ainfo_farena(sarena);

	Str8Gen result = str8gen_make(buffer);
	U4 line_num = 0;
	for slice_iter(lines, line)
	{
	#define fmt_entry(label, value) { lit(label), value }
		++ line_num;
		Str8 str_line_num  = str8_from_u32(sinfo, line_num,            10, 0, 0);
		Str8 str_chunk_num = str8_from_u32(sinfo, cast(U4, line->len), 10, 0, 0);
		str8gen_append_fmt(& result, "Line <line_num> - Chunks <chunk_num>:\n"
		,	fmt_entry("line_num",  str_line_num)
		,	fmt_entry("chunk_num", str_chunk_num)
		);
		for slice_iter(line[0], chunk)
		{
			Str8 id;
			switch (chunk->ptr[0])
			{
				case WATL_Tok_Space: id = lit("Space");   break;
				case WATL_Tok_Tab:   id = lit("Tab");     break;
				default:             id = lit("Visible"); break;
			}
			Str8 str_chunk_len = str8_from_u32(sinfo, cast(U4, chunk->len), 10, 0, 0);
			str8gen_append_fmt(& result, "\t<id>(<size>): '<chunk>'\n"
			,	fmt_entry("id",    id)
			,	fmt_entry("size",  str_chunk_len)
			,	fmt_entry("chunk", chunk[0])
			);
		}
		farena_reset(& sarena);
	#undef fmt_entry_u32
	}
	return (Str8){ result.ptr, result.len };
}
#pragma endregion WATL

#pragma endregion Implementation

int main(void)
{
	os_init();

	VArena_R vm_file = varena_make(.reserve_size = giga(4), .flags = VArenaFlag_NoLargePages);
	FileOpInfo file  = file_read_contents(lit("watl.v0.llvm.lottes_hybrid.c"), .backing = ainfo_varena(vm_file));
	slice_assert(file.content);

	Arena_R a_msgs = arena_make();
	Arena_R a_toks = arena_make();
	WATL_LexInfo lex_res = watl_lex(pcast(Str8, file.content),
		.ainfo_msgs = ainfo_arena(a_msgs),
		.ainfo_toks = ainfo_arena(a_toks),
	);
	assert((lex_res.signal & WATL_LexStatus_MemFail_SliceConstraintFail) == 0);

	Arena_R str_cache_kt1_ainfo = arena_make();
	Str8Cache str_cache = str8cache_make(
		.str_reserve    = ainfo_arena(arena_make(.reserve_size = mega(256))),
		.cell_reserve   = ainfo_arena(str_cache_kt1_ainfo),
		.tbl_backing    = ainfo_arena(str_cache_kt1_ainfo),
		.cell_pool_size = kilo(8),
		.table_size     = kilo(64),
	);

	Arena_R a_lines = arena_make();
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
	file_write_str8(lit("watl.v0.lottes.c.listing.txt"), listing);
	return 0;
}

#pragma clang diagnostic pop
