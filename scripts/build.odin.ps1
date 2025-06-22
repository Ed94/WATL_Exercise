$path_root  = split-path -Path $PSScriptRoot -Parent
$path_build = join-path $path_root 'build'
$path_code  = join-path $path_root 'code'

$path_source = join-path $PSScriptRoot 'build.odin.odin'
$exe         = join-path $path_build   'build_win32.exe'

if ((test-path $path_build) -eq $false) {
	new-item -itemtype directory -path $path_build
}

$odin = 'odin.exe'

$command_build = 'build'

$flag_debug                 = '-debug'
$flag_file                  = '-file'
$flag_dyn_map_calls         = '-dynamic-map-calls'
$flag_no_bounds_check       = '-no-bounds-check'
$flag_no_threaded_checker   = '-no-threaded-checker'
$flag_no_type_assert        = '-no-type-assert'
$flag_optimize_none         = '-o:none'
$flag_output_path           = '-out='
$flag_default_allocator_nil = '-default-to-nil-allocator'

$need_rebuild = $false
if (-not (test-path $exe)) { $need_rebuild = $true } 
else {
	$source_hash = (get-filehash $path_source -algorithm MD5).Hash
	$exe_hash    = (get-filehash $exe         -algorithm MD5).Hash
	if ($exe_hash -ne $source_hash) { $need_rebuild = $true }
}
push-location $path_root
$build_args = @()
$build_args += $command_build
$build_args += $path_source
$build_args += $flag_file
# $build_args += $flag_debug
$build_args += $flag_optimize_none
$build_args += $flag_no_bounds_check
$build_args += $flag_no_threaded_checker
$build_args += $flag_no_type_assert
$build_args += $flag_dyn_map_calls
$build_args += $flag_default_allocator_nil
$build_args += $flag_output_path + $exe
if ($need_rebuild) { & $odin $build_args }
pop-location
& $exe
