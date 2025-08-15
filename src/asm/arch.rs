use crate::object;

/// A CPU architecture.
#[derive(Eq, Hash, Copy, Clone, Debug, PartialEq)]
pub enum Arch {
    Riscv32,
    Riscv64
}

impl Arch {
    /// The size of an address value for this architecture.
    #[inline(always)]
    pub const fn address_size(self) -> AddressSize {
        match self {
            Self::Riscv32 => AddressSize::U32,
            Self::Riscv64 => AddressSize::U64,
        }
    }

    /// Convert brik Arch into `object::Architecture`
    #[inline(always)]
    pub const fn into_object_architecture(self) -> object::Architecture {
        match self {
            Self::Riscv32 => object::Architecture::Riscv32,
            Self::Riscv64 => object::Architecture::Riscv64,
        }
    }

    /// Get the maximum call range for this architecture
    #[inline(always)]
    pub const fn max_call_range(self) -> i64 {
        match self {
            // both architectures have the same range due to instruction encoding
            Self::Riscv32 | Self::Riscv64 => 1i64 << 31, // +-2GB
        }
    }

    /// Get the maximum branch range for this architecture
    #[inline(always)]
    pub const fn max_branch_range(self) -> i64 {
        match self {
            Arch::Riscv32 | Arch::Riscv64 => 4096, // +-4KB
        }
    }

    /// Get the maximum JAL range for this architecture
    #[inline(always)]
    pub const fn max_jal_range(self) -> i64 {
        match self {
            Arch::Riscv32 | Arch::Riscv64 => 1048576, // +-1MB
        }
    }
}

/// The size of an address value for an architecture.
#[repr(u8)]
#[derive(Eq, Hash, Copy, Clone, Debug, PartialEq)]
pub enum AddressSize {
    U8  = 1,
    U16 = 2,
    U32 = 4,
    U64 = 8,
}

impl AddressSize {
    /// The size in bytes of an address value.
    #[inline(always)]
    pub const fn bytes(self) -> u8 {
        self as _
    }

    /// The size in bits of an address value.
    #[inline(always)]
    pub const fn bits(self) -> u8 {
        self.bytes() * 8
    }
}

