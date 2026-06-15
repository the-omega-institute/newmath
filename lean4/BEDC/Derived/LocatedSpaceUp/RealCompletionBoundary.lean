import BEDC.Derived.LocatedSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSpaceCarrier_real_completion_boundary [AskSetup] [PackageSetup]
    {X R A G W Q E H C P N requestRead windowRead readbackRead sealRead replayRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory X ∧ UnaryHistory R ∧ UnaryHistory W ∧ UnaryHistory Q ∧
      UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C) →
      Cont X R requestRead →
        Cont requestRead W windowRead →
          Cont windowRead Q readbackRead →
            Cont readbackRead E sealRead →
              Cont H C replayRead →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row R ∨ hsame row W ∨ hsame row Q ∨
                          hsame row E ∨ hsame row sealRead ∨ Cont H C replayRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rows requestRoute windowRoute readbackRoute sealRoute replayRoute namePkg
  obtain ⟨xUnary, rUnary, wUnary, qUnary, eUnary, _hUnary, _cUnary⟩ := rows
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed xUnary rUnary requestRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row R ∨ hsame row W ∨ hsame row Q ∨
              hsame row E ∨ hsame row sealRead ∨ Cont H C replayRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, namePkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LocatedSpaceUp
