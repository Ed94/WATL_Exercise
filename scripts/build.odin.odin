package build

//region Script Grime
import mem "core:mem"
import vmem "core:mem/virtual"
import os "core:os/os2"
import "core:fmt"
import _strings "core:strings"
	StrGen      :: _strings.Builder
	strgen_init :: _strings.builder_init
	strgen_join :: _strings.join

join_path       :: #force_inline proc(elems : ..string) -> string { res, _ := os.join_path(transmute([]string)elems, context.allocator); return transmute(string)res }
get_working_dir :: #force_inline proc()                 -> string { res, _ := os.get_working_directory(context.allocator);               return transmute(string)res }

join_str :: #force_inline proc(elems  : ..string) -> string { 
	gen : StrGen; strgen_init(& gen, context.allocator)
	res, _ := strgen_join(elems, "")
	return res
}

// For a beakdown of any flag, type <odin_compiler> <command> -help
command_build  :: "build"
command_check  :: "check"
command_query  :: "query"
command_report :: "report"
command_run    :: "run"

flag_build_mode                :: "-build-mode:"
flag_build_mode_dll            :: "-build-mode:dll"
flag_collection                :: "-collection:"
flag_file                      :: "-file"
flag_debug                     :: "-debug"
flag_define                    :: "-define:"
flag_default_allocator_nil     :: "-default-to-nil-allocator"
flag_disable_assert            :: "-disable-assert"
flag_dynamic_map_calls         :: "-dynamic-map-calls"
flag_extra_assembler_flags     :: "-extra_assembler-flags:"
flag_extra_linker_flags        :: "-extra-linker-flags:"
flag_ignore_unknown_attributes :: "-ignore-unknown-attributes"
flag_keep_temp_files           :: "-keep-temp-files"
flag_max_error_count           :: "-max-error-count:"
flag_micro_architecture_native :: "-microarch:native"
flag_no_bounds_check           :: "-no-bounds-check"
flag_no_crt                    :: "-no-crt"
flag_no_entrypoint             :: "-no-entry-point"
flag_no_thread_local           :: "-no-thread-local"
flag_no_thread_checker         :: "-no-threaded-checker"
flag_output_path               :: "-out="
flag_optimization_level        :: "-opt:"
flag_optimize_none             :: "-o:none"
flag_optimize_minimal          :: "-o:minimal"
flag_optimize_size             :: "-o:size"
flag_optimize_speed            :: "-o:speed"
falg_optimize_aggressive       :: "-o:aggressive"
flag_pdb_name                  :: "-pdb-name:"
flag_sanitize_address          :: "-sanitize:address"
flag_sanitize_memory           :: "-sanitize:memory"
flag_sanitize_thread           :: "-sanitize:thread"
flag_subsystem                 :: "-subsystem:"
flag_show_debug_messages       :: "-show-debug-messages"
flag_show_timings              :: "-show-timings"
flag_show_more_timings         :: "-show-more-timings"
flag_show_system_calls         :: "-show-system-calls"
flag_target                    :: "-target:"
flag_thread_count              :: "-thread-count:"
flag_use_lld                   :: "-linker:lld"
flag_use_rad_link              :: "-linker:radlink"
flag_use_separate_modules      :: "-use-separate-modules"
flag_vet_all                   :: "-vet"
flag_vet_unused_entities       :: "-vet-unused"
flag_vet_semicolon             :: "-vet-semicolon"
flag_vet_shadow_vars           :: "-vet-shadowing"
flag_vet_using_stmt            :: "-vet-using-stmt"

flag_microarch_zen5 :: "--microarch:znver5"

flag_msvc_link_disable_dynamic_base :: "/DYNAMICBASE:NO"
flag_msvc_link_base_address         :: "/BASE:"
flag_msvc_link_fixed_base_address   :: "/FIXED"
flag_msvc_link_stack_size           :: "/STACK"
flag_msvc_link_debug                :: "/DEBUG"

msvc_link_default_base_address :: 0x180000000
//endregion Script Grime

build :: proc(working_dir : string, args : []string) -> (stdout : string, stderr : string) { 
	fmt.println("Building:", args)
	res, errs : []byte; _, res, errs, _ = os.process_exec({ working_dir = working_dir, command = args}, context.allocator)
	return transmute(string)res, transmute(string)errs;
}

main :: proc() {
	varena : vmem.Arena; _ = vmem.arena_init_growing(& varena, mem.Megabyte * 64 ); context.allocator = vmem.arena_allocator(& varena)
	exe_odin :: "odin.exe"

	path_root     := get_working_dir()
	path_build    := join_path(path_root,     "build")
	path_odin_src := join_path(path_root,     "Odin")
	file_source   := join_path(path_odin_src, "watl.v0.win32.odin")
	file_exe      := join_path(path_build,    "watl.v0.exe")

	res, errs := build(path_build, {
		exe_odin,
		command_build,
		file_source,
		flag_file,
		join_str(flag_output_path, file_exe),
		flag_optimize_none,
		flag_default_allocator_nil,
		flag_debug,
		flag_microarch_zen5,
		flag_no_thread_checker,
		flag_show_timings,
		flag_use_rad_link,
		join_str(flag_subsystem, "console"),
	})
	fmt.println(res)
	fmt.println(errs)
}
