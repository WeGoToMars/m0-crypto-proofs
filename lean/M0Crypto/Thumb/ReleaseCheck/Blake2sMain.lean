import M0Crypto.Thumb.ReleaseCheck.Blake2sCases

/-! `main` of the BLAKE2s asset's native release-check executable (`lake exe release_check`). -/

def main : IO UInt32 := M0Crypto.Thumb.ReleaseCheck.exeMain M0Crypto.Thumb.ReleaseCheck.b2sAllChecks
