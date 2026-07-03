import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorRealSealBridge [AskSetup] [PackageSetup]
    {epsilon W R D A sigma H C P N epsilonWindow windowRegular regularDyadic
      dyadicSelector selectorSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalStreamTailSelectorCarrier epsilon W R D A sigma H C P N bundle pkg →
      Cont epsilon W epsilonWindow →
        Cont epsilonWindow R windowRegular →
          Cont windowRegular D regularDyadic →
            Cont regularDyadic sigma dyadicSelector →
              Cont dyadicSelector A selectorSeal →
                PkgSig bundle selectorSeal pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row selectorSeal ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                          hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                            hsame row P ∨ hsame row N ∨ hsame row epsilonWindow ∨
                              hsame row windowRegular ∨ hsame row regularDyadic ∨
                                hsame row dyadicSelector ∨ hsame row selectorSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont epsilon W epsilonWindow ∧
                          Cont epsilonWindow R windowRegular ∧
                            Cont windowRegular D regularDyadic ∧
                              Cont regularDyadic sigma dyadicSelector ∧
                                Cont dyadicSelector A selectorSeal ∧
                                  PkgSig bundle selectorSeal pkg)
                      hsame ∧
                    UnaryHistory selectorSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier epsilonRoute regularRoute dyadicRoute selectorRoute sealRoute sealPkg
  obtain ⟨epsilonUnary, windowUnary, regularUnary, dyadicUnary, selectorUnary,
    sigmaUnary, _handoffUnary, _contReplayUnary, _pkgUnary, _localUnary, _packageProof⟩ :=
    carrier
  have epsilonWindowUnary : UnaryHistory epsilonWindow :=
    unary_cont_closed epsilonUnary windowUnary epsilonRoute
  have windowRegularUnary : UnaryHistory windowRegular :=
    unary_cont_closed epsilonWindowUnary regularUnary regularRoute
  have regularDyadicUnary : UnaryHistory regularDyadic :=
    unary_cont_closed windowRegularUnary dyadicUnary dyadicRoute
  have dyadicSelectorUnary : UnaryHistory dyadicSelector :=
    unary_cont_closed regularDyadicUnary sigmaUnary selectorRoute
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed dyadicSelectorUnary selectorUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row sigma ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row epsilonWindow ∨
                  hsame row windowRegular ∨ hsame row regularDyadic ∨
                    hsame row dyadicSelector ∨ hsame row selectorSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilon W epsilonWindow ∧
              Cont epsilonWindow R windowRegular ∧ Cont windowRegular D regularDyadic ∧
                Cont regularDyadic sigma dyadicSelector ∧
                  Cont dyadicSelector A selectorSeal ∧ PkgSig bundle selectorSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨selectorSeal, hsame_refl selectorSeal, selectorSealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, epsilonRoute, regularRoute, dyadicRoute, selectorRoute, sealRoute,
          sealPkg⟩
  }
  exact ⟨cert, selectorSealUnary⟩

end BEDC.Derived.CofinalStreamTailSelectorUp
