import BEDC.Derived.BoundedCauchyFilterUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedCauchyFilterCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source boundedFace dyadic windows readback realSeal transport replay provenance localName
      sourceRead toleranceRead windowRead rationalRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source ∧ UnaryHistory boundedFace ∧ UnaryHistory dyadic ∧
        UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory realSeal ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory localName ∧ PkgSig bundle provenance pkg →
      Cont source boundedFace sourceRead →
        Cont sourceRead dyadic toleranceRead →
          Cont toleranceRead windows windowRead →
            Cont windowRead readback rationalRead →
              Cont rationalRead realSeal sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row source ∨ hsame row boundedFace ∨ hsame row dyadic ∨
                          hsame row windows ∨ hsame row readback ∨ hsame row realSeal ∨
                            hsame row sealRead)
                      (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory sourceRead ∧ UnaryHistory toleranceRead ∧
                      UnaryHistory windowRead ∧ UnaryHistory rationalRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute toleranceRoute windowRoute rationalRoute sealRoute sealPkg
  obtain ⟨sourceUnary, boundedFaceUnary, dyadicUnary, windowsUnary, readbackUnary,
    realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary boundedFaceUnary sourceRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceReadUnary dyadicUnary toleranceRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceReadUnary windowsUnary windowRoute
  have rationalReadUnary : UnaryHistory rationalRead :=
    unary_cont_closed windowReadUnary readbackUnary rationalRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rationalReadUnary realSealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row boundedFace ∨ hsame row dyadic ∨
              hsame row windows ∨ hsame row readback ∨ hsame row realSeal ∨
                hsame row sealRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, sealPkg⟩
  }
  exact
    ⟨cert, sourceReadUnary, toleranceReadUnary, windowReadUnary, rationalReadUnary,
      sealReadUnary⟩

end BEDC.Derived.BoundedCauchyFilterUp
