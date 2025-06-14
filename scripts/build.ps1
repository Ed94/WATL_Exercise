$misc = Join-Path $PSScriptRoot 'helpers/misc.psm1'
import-module $misc

$devshell  = join-path $PSScriptRoot 'helpers/devshell.ps1'
$path_root = Get-ScriptRepoRoot

if ($IsWindows) {
	& $devshell -arch amd64
}

# https://learn.microsoft.com/en-us/cpp/build/reference/compiler-options-listed-by-category?view=msvc-170
$flag_all_c                        = '/TC'
$flag_c11                          = '/std:c11'
$flag_c23                          = '/std:c23'
$flag_all_cpp                      = '/TP'
$flag_compile                      = '/c'
$flag_charset_utf8                 = '/utf-8'
$flag_debug                        = '/Zi'
$flag_define                       = '/D'
$flag_exceptions_disabled          = '/EHsc-'
$flag_RTTI_disabled                = '/GR-'
$flag_include                      = '/I'
$flag_full_src_path                = '/FC'
$flag_asm_listing_file             = '/FAs'
$flag_nologo                       = '/nologo'
$flag_dll                          = '/LD'
$flag_dll_debug                    = '/LDd'
$flag_linker                       = '/link'
# $flag_link_lib                     = '/lib'
$flag_link_dll                     = '/DLL'
$flag_link_no_incremental          = '/INCREMENTAL:NO'
$flag_link_mapfile                 = '/MAP:'
$flag_link_optimize_references     = '/OPT:REF'
$flag_link_win_debug               = '/DEBUG'
$flag_link_win_pdb                 = '/PDB:'
$flag_link_win_machine_32          = '/MACHINE:X86'
$flag_link_win_machine_64          = '/MACHINE:X64'
$flag_link_win_path_output         = '/OUT:'
$flag_link_win_rt_dll              = '/MD'
$flag_link_win_rt_dll_debug        = '/MDd'
$flag_link_win_rt_static           = '/MT'
$flag_link_win_rt_static_debug     = '/MTd'
$flag_link_win_subsystem_console   = '/SUBSYSTEM:CONSOLE'
$flag_link_win_subsystem_windows   = '/SUBSYSTEM:WINDOWS'
$flag_no_optimization              = '/Od'
$flag_optimize_speed_max           = '/Ox'
$flag_optimize_fast                = '/O2'
$flag_optimize_size                = '/O1'
$flag_optimize_intrinsics          = '/Oi'
$flag_optimized_debug_forceinline  = '/d2Obforceinline'
$flag_optimized_debug              = '/Zo'
$flag_preprocess_to_file           = '/P'
$flag_preprocess_preserve_comments = '/C'
# $flag_out_name                     = '/OUT:'
$flag_path_interm                  = '/Fo'
$flag_path_debug                   = '/Fd'
$flag_path_output                  = '/Fe'
$flag_preprocess_conform           = '/Zc:preprocessor'
$flag_sanitize_address             = '/fsanitize=address'
$flag_updated_cpp_macro            = "/Zc:__cplusplus"
$flag_set_stack_size               = '/F'
$flag_syntax_only                  = '/Zs'
$flag_wall                         = '/Wall'
$flag_warnings_as_errors           = '/WX'
$flag_lib_list                     = '/LIST'
 
$archiver = 'lib'
$compiler = 'cl'
$linker   = 'link'

$path_build = join-path $path_root 'build'
if ( -not(test-path -Path $path_build) ) {
	new-item -ItemType Directory -Path $path_build
}

push-location $path_build

$compiler_args = @()
$compiler_args += $flag_nologo

# Constraints on interpeting all files as C code
$compiler_args += $flag_all_c
$compiler_args += $flag_c11
# Constraints on C program code-gen 
$compiler_args += $flag_exceptions_disabled
$compiler_args += $flag_RTTI_disabled
$compiler_args += $flag_preprocess_conform
# $compiler_args += $flag_sanitize_address

$compiler_args += $flag_wall

# Set charset encoding for both execution and source to UTF-8
$compiler_args += $flag_charset_utf8

# Specifing output pathing
$compiler_args += ( $flag_path_interm + $path_build + '\' )
$compiler_args += ( $flag_path_output + $path_build + '\' )

# Dump preprocess file
if ($false) {
	$compiler_args += $flag_preprocess_to_file
	$compiler_args += $flag_preprocess_preserve_comments
}

# Diagnostic logging
$compiler_args += $flag_full_src_path
$compiler_args += $flag_asm_listing_file

# $compiler_args += $flag_optimize_speed_max
$compiler_args += $flag_optimize_size
# $compiler_args += $flag_optimize_intrinsics
# $compiler_args += $flag_no_optimization

# Debug setup
$compiler_args += ($flag_define + 'BUILD_DEBUG')
$compiler_args += $flag_debug
$compiler_args += ( $flag_path_debug + $path_build + '\' )
$compiler_args += $flag_link_win_rt_static

# Include setup
$compiler_args += ($flag_include + $path_root)

# Specify unit to compile
$unit           = join-path $path_root 'C\watl.v0.msvc.c'
$compiler_args += $flag_compile, $unit

# Diagnoistc print for the args
$compiler_args | ForEach-Object { Write-Host $_ }
write-host

# Compile the unit
& $compiler $compiler_args

$binary = join-path $path_build 'watl.v0.msvc.exe'
$object = join-path $path_build 'watl.v0.msvc.obj'

$pdb = join-path $path_build 'watl.v0.msvc.pdb'
$map = join-path $path_build 'watl.v0.msvc.map'

if ($true) {
	$linker_args = @()
	$linker_args += $flag_nologo
	$linker_args += $flag_link_win_machine_64
	$linker_args += $flag_link_no_incremental
	$linker_args += ($flag_link_win_path_output + $binary)

	$linker_args += $flag_link_win_debug
	$linker_args += $flag_link_win_pdb + $pdb
	$linker_args += $flag_link_mapfile + $map

	$linker_args += $object

	# Diagnoistc print for the args
	$linker_args | ForEach-Object { Write-Host $_ }
	write-host

	& $linker $linker_args
}

Pop-Location
