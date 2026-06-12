import BEDC.Derived.DyadicNestedIntervalSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicNestedIntervalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicNestedIntervalSelectorNamecertObligations [AskSetup] [PackageSetup]
    {I D S R E H C P N selectorRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I →
      UnaryHistory D →
        UnaryHistory S →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory H →
                UnaryHistory C →
                  UnaryHistory P →
                    UnaryHistory N →
                      Cont I D S →
                        Cont S R selectorRead →
                          Cont selectorRead E replayRead →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row E ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row I ∨ hsame row D ∨ hsame row S ∨
                                        hsame row R ∨ hsame row E ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                                            hsame row selectorRead ∨
                                              hsame row replayRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont I D S ∧
                                        Cont S R selectorRead ∧
                                          Cont selectorRead E replayRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle N pkg)
                                    hsame ∧ UnaryHistory selectorRead ∧
                                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryI unaryD unaryS unaryR unaryE _unaryH _unaryC _unaryP _unaryN
    nestedRoute selectorRoute replayRoute provenancePkg namePkg
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed unaryS unaryR selectorRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed selectorUnary unaryE replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row E ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row selectorRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I D S ∧ Cont S R selectorRead ∧
              Cont selectorRead E replayRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨hsame_refl E, unaryE⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, nestedRoute, selectorRoute, replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, selectorUnary, replayUnary⟩

end BEDC.Derived.DyadicNestedIntervalSelectorUp
