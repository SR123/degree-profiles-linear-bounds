/- Cycle 010: direct coordinate identities checked by kernel reduction. -/
import RankThreeRowData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SelfContainedCycle010
open SelfContainedCycle009
theorem reconstruction_bits : ∀ x : Raw,
    combineBits (Erow x) (fun i => combineBits (Lrow i) Zbits) = Zbits x := by decide +kernel

theorem compression_bits : ∀ i : ImageCoord,
    combineBits (Lrow i) (fun x => combineBits (Zrow x)
      (fun y => combineBits (Arow y) Ebits)) = Bbits i := by decide +kernel

end SelfContainedCycle010
