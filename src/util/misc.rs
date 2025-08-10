pub fn generate_riscv_attrs(vendor: &str, arch: &str) -> Vec<u8> {
    let mut bytes = Vec::new();

    // Format version
    bytes.push(0x41);

    // Placeholder for total length (4 bytes)
    bytes.extend_from_slice(&[0, 0, 0, 0]);

    // Vendor string + null terminator
    bytes.extend_from_slice(vendor.as_bytes());
    bytes.push(0x00);

    // Tag_File (0x01)
    bytes.push(0x01);

    // Placeholder for Tag_File length (4 bytes)
    let tag_file_len_pos = bytes.len();
    bytes.extend_from_slice(&[0, 0, 0, 0]);

    // Tag_RISCV_arch (0x17)
    bytes.push(0x18);

    // Architecture string bytes (no null terminator)
    bytes.extend(arch.as_bytes());

    // Tag_File length = bytes after tag_file_len_pos + 4 (the length field itself)
    let tag_file_len = (bytes.len() - (tag_file_len_pos + 4)) as u32;
    bytes[tag_file_len_pos..tag_file_len_pos + 4]
        .copy_from_slice(&tag_file_len.to_le_bytes());

    // total length = bytes after version byte and total length field (5 bytes)
    let total_len = (bytes.len() - 5) as u32;
    bytes[1..5].copy_from_slice(&total_len.to_le_bytes());

    bytes
}
