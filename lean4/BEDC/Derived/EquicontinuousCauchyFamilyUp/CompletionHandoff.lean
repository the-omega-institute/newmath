import BEDC.Derived.EquicontinuousCauchyFamilyUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EquicontinuousCauchyFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuousCauchyFamilyCarrier_completion_handoff [AskSetup] [PackageSetup]
    {K U M T W R D A H C P N uniformRead modulusRead thresholdRead windowRead readbackRead
      toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory K ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory T ∧
      UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory A) →
      Cont K U uniformRead →
        Cont uniformRead M modulusRead →
          Cont modulusRead T thresholdRead →
            Cont thresholdRead W windowRead →
              Cont windowRead R readbackRead →
                Cont readbackRead D toleranceRead →
                  Cont toleranceRead A sealRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row U ∨ hsame row M ∨
                                hsame row T ∨ hsame row W ∨ hsame row R ∨
                                  hsame row D ∨ hsame row A ∨ hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont K U uniformRead ∧
                                Cont uniformRead M modulusRead ∧
                                  Cont modulusRead T thresholdRead ∧
                                    Cont thresholdRead W windowRead ∧
                                      Cont windowRead R readbackRead ∧
                                        Cont readbackRead D toleranceRead ∧
                                          Cont toleranceRead A sealRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory sealRead ∧ UnaryHistory thresholdRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rows uniformRoute modulusRoute thresholdRoute windowRoute readbackRoute toleranceRoute
    sealRoute provenancePkg namePkg
  obtain ⟨kUnary, uUnary, mUnary, tUnary, wUnary, rUnary, dUnary, aUnary⟩ := rows
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed kUnary uUnary uniformRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed uniformUnary mUnary modulusRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed modulusUnary tUnary thresholdRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed thresholdUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary dUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary aUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row U ∨ hsame row M ∨ hsame row T ∨
              hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K U uniformRead ∧ Cont uniformRead M modulusRead ∧
              Cont modulusRead T thresholdRead ∧ Cont thresholdRead W windowRead ∧
                Cont windowRead R readbackRead ∧ Cont readbackRead D toleranceRead ∧
                  Cont toleranceRead A sealRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, uniformRoute, modulusRoute, thresholdRoute, windowRoute, readbackRoute,
          toleranceRoute, sealRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, sealUnary, thresholdUnary⟩

end BEDC.Derived.EquicontinuousCauchyFamilyUp
