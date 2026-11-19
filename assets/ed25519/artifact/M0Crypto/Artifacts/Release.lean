/-! The single-artifact slot that shared modules import (`Release.B`, the listing). The Ed25519
asset has two builds, each with its own artifact module (`Ed25519Compact`, `Ed25519Fast`); its
judgments take the build's bytes as a parameter (`Release.Ed25519Build`). This slot is empty, so
nothing stated over it says anything about the Ed25519 bytes. Not generated. -/

namespace M0Crypto.Artifacts.Release

def sha256 : String := ""
def codeRanges : List (Nat × Nat) := []
def dataRanges : List (Nat × Nat) := []
def size : Nat := 0
def bytes : List (BitVec 8) := []
theorem bytes_length : bytes.length = size := rfl

end M0Crypto.Artifacts.Release
