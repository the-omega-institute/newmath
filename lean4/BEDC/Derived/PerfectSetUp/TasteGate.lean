import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.PerfectSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

inductive PerfectSetUp : Type where
  | mk (T K D W R E H C P N : BHist) : PerfectSetUp
  deriving DecidableEq

def perfectSetFields : PerfectSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PerfectSetUp.mk T K D W R E H C P N => [T, K, D, W, R, E, H, C, P, N]

theorem PerfectSetCarrier_derived_point_nonescape [AskSetup] [PackageSetup]
    {T K D W R E H C P N route sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    perfectSetFields (PerfectSetUp.mk T K D W R E H C P N) =
        [T, K, D, W, R, E, H, C, P, N] →
      Cont T K D →
        Cont D W R →
          Cont R E sealRow →
            Cont sealRow H route →
              PkgSig bundle N pkg →
                hsame route H ∨ hsame route sealRow →
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row route ∧
                        ∃ packet : PerfectSetUp,
                          packet = PerfectSetUp.mk T K D W R E H C P N ∧
                            perfectSetFields packet = [T, K, D, W, R, E, H, C, P, N])
                    (fun row : BHist =>
                      Cont T K D ∧ Cont D W R ∧ Cont R E sealRow ∧
                        Cont sealRow H row)
                    (fun row : BHist =>
                      PkgSig bundle N pkg ∧ (hsame row H ∨ hsame row sealRow))
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldsEq topologyCompact derivedWindow realSeal structuralRoute pkgSig publicRoute
  let packet := PerfectSetUp.mk T K D W R E H C P N
  have sourceRoute :
      hsame route route ∧
        ∃ packet : PerfectSetUp,
          packet = PerfectSetUp.mk T K D W R E H C P N ∧
            perfectSetFields packet = [T, K, D, W, R, E, H, C, P, N] :=
    ⟨hsame_refl route, Exists.intro packet ⟨rfl, fieldsEq⟩⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro route sourceRoute
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨topologyCompact, derivedWindow, realSeal, structuralRoute⟩
    ledger_sound := by
      intro _row source
      cases source.left
      exact ⟨pkgSig, publicRoute⟩
  }

end BEDC.Derived.PerfectSetUp
