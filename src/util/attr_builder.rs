//! Attribute builder for metadata sections (i.e. ".riscv.attributes")

#[derive(Debug)]
pub struct RiscvAttrsBuilder {
    vendor: Vec<u8>,
    tags: Vec<(u8, Vec<u8>)>,
}

impl RiscvAttrsBuilder {
    /// Create a new builder with vendor string (usually "riscv")
    #[inline(always)]
    pub fn new(vendor: &str) -> Self {
        Self {
            vendor: vendor.as_bytes().to_owned(),
            tags: Vec::new(),
        }
    }

    /// Add the architecture string tag (tag 0x18)
    #[inline(always)]
    pub fn arch(mut self, isa_str: &str) -> Self {
        self.tags.push((0x18, isa_str.as_bytes().to_vec()));
        self
    }

    /// Add a custom tag (tag byte and raw bytes)
    #[inline(always)]
    pub fn tag(mut self, tag_byte: u8, data: &[u8]) -> Self {
        self.tags.push((tag_byte, data.to_vec()));
        self
    }

    /// Build the final attribute bytes
    pub fn build(self) -> Vec<u8> {
        let mut bytes = Vec::new();

        // format version
        bytes.push(0x41);

        // placeholder for total length
        bytes.extend(&[0, 0, 0, 0]);

        // vendor + \0
        bytes.extend(&self.vendor);
        bytes.push(0x00);

        // Tag_File (0x01)
        bytes.push(0x01);

        // placeholder for Tag_File length
        let tag_file_len_pos = bytes.len();
        bytes.extend(&[0, 0, 0, 0]);

        for (tag_byte, data) in self.tags {
            bytes.push(tag_byte);
            bytes.extend(&data);
        }

        // fill in Tag_File length
        let tag_file_len = (bytes.len() - (tag_file_len_pos + 4)) as u32;
        bytes[tag_file_len_pos..tag_file_len_pos + 4]
            .copy_from_slice(&tag_file_len.to_le_bytes());

        // fill in total length (from after version byte and total length field, i.e. 5 bytes)
        let total_len = (bytes.len() - 5) as u32;
        bytes[1..5].copy_from_slice(&total_len.to_le_bytes());

        bytes
    }
}
