import M0Crypto.Thumb.ReleaseCheck.ChaCha20Cases

/-! `main` of the ChaCha20-Poly1305 asset's native release-check executable
(`lake exe release_check`). -/

def main : IO UInt32 := M0Crypto.Thumb.ReleaseCheck.exeMain M0Crypto.Thumb.ReleaseCheck.allChecks
