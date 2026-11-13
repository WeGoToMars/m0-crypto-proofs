import M0Crypto.Thumb.ReleaseCheck.X25519Cases

/-! `main` of the X25519 asset's native release-check executable (`lake exe release_check`). -/

def main : IO UInt32 := M0Crypto.Thumb.ReleaseCheck.exeMain M0Crypto.Thumb.ReleaseCheck.X25519.allChecks
