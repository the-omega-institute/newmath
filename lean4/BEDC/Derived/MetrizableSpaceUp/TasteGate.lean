import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.MetrizableSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

inductive MetrizableSpaceUp : Type where
  | mk (T M B W R E H C P N : BHist) : MetrizableSpaceUp
  deriving DecidableEq

def metrizableSpaceFields : MetrizableSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetrizableSpaceUp.mk T M B W R E H C P N => [T, M, B, W, R, E, H, C, P, N]

theorem MetrizableSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {T M B W R E H C P N route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    metrizableSpaceFields (MetrizableSpaceUp.mk T M B W R E H C P N) =
        [T, M, B, W, R, E, H, C, P, N] →
      Cont T B W →
        Cont M W R →
          Cont R E route →
            PkgSig bundle N pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row route ∧
                    ∃ packet : MetrizableSpaceUp,
                      packet = MetrizableSpaceUp.mk T M B W R E H C P N ∧
                        metrizableSpaceFields packet = [T, M, B, W, R, E, H, C, P, N])
                (fun row : BHist => Cont T B W ∧ Cont M W R ∧ Cont R E row)
                (fun row : BHist => hsame row route ∧ PkgSig bundle N pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldsEq topologyWindow metricReadback realRoute pkgSig
  let packet := MetrizableSpaceUp.mk T M B W R E H C P N
  have sourceRoute :
      hsame route route ∧
        ∃ packet : MetrizableSpaceUp,
          packet = MetrizableSpaceUp.mk T M B W R E H C P N ∧
            metrizableSpaceFields packet = [T, M, B, W, R, E, H, C, P, N] :=
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
      exact ⟨topologyWindow, metricReadback, realRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

end BEDC.Derived.MetrizableSpaceUp
