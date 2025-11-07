package watl

import "core:os/os2"
import "core:mem/virtual"
import "core:mem"


main :: proc()
{
	os_init()

	// Note(Ed): Possible compiler bug, cannot resolve proc map with named arguments.

	vm_file: virtual.Arena; virtual.arena_init_static(& vm_file, reserved = mem.Gigabytes * 4)
	data, err := os2.read_entire_file_from_path("watl.v0.ideomatic.odin", virtual.arena_allocator(& vm_file), )
	assert(err != .None)

	

	a_msgs  := arena_make()
	a_toks  := arena_make()
	// lex_res := watl_lex(transmute(string) file.content, 
	// 	ainfo_msgs = ainfo(a_msgs), 
	// 	ainfo_toks = ainfo(a_toks),
	// )
	lex_res := watl_lex(transmute(string) file.content, 
		ainfo(a_msgs), 
		ainfo(a_toks),
	)
	assert(lex_res.signal & { .MemFail_SliceConstraintFail } == {})

	str8_cache_kt1_ainfo := arena_make()
	str_cache := str8cache_make(
		str_reserve    = ainfo(arena_make()),
		cell_reserve   = ainfo(str8_cache_kt1_ainfo),
		tbl_backing    = ainfo(str8_cache_kt1_ainfo),
		cell_pool_size = Kilo * 4,
		table_size     = Kilo * 32,
	)

	a_lines := arena_make()
	// parse_res := watl_parse(lex_res.toks,
	// 	ainfo_msgs  = ainfo(a_msgs),
	// 	ainfo_nodes = ainfo(a_toks),
	// 	ainfo_lines = ainfo(a_lines),
	// 	str_cache   = & str_cache
	// )
	parse_res := watl_parse(lex_res.toks,
		ainfo(a_msgs),
		ainfo(a_toks),
		ainfo(a_lines),
		& str_cache
	)
	assert(parse_res.signal & { .MemFail_SliceConstraintFail } == {})

	arena_reset(a_msgs)
	arena_reset(a_toks)
	listing := watl_dump_listing(ainfo(a_msgs), parse_res.lines)
	file_write_str8("watl.v0.win32.odin.listing.txt", listing)
	return
}