import BEDC.Derived.PhysicalInductionGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PhysicalInductionGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PhysicalInductionGateCarrier [AskSetup] [PackageSetup]
    (S O M Pi F Cn B Y H R P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  physicalInductionGateFields (PhysicalInductionGateUp.mk S O M Pi F Cn B Y H R P N) =
      [S, O, M, Pi, F, Cn, B, Y, H, R, P, N] ∧
    UnaryHistory S ∧ UnaryHistory O ∧ UnaryHistory M ∧ UnaryHistory Pi ∧
      UnaryHistory F ∧ UnaryHistory Cn ∧ UnaryHistory B ∧ UnaryHistory Y ∧
        UnaryHistory H ∧ UnaryHistory R ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle N pkg

theorem PhysicalInductionGateNameCertObligations [AskSetup] [PackageSetup]
    {S O M Pi F Cn B Y H R P N fitRead stabilityRead failureRead descentRead named :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PhysicalInductionGateCarrier S O M Pi F Cn B Y H R P N bundle pkg ->
      Cont S F fitRead ->
        Cont fitRead Cn stabilityRead ->
          Cont stabilityRead B failureRead ->
            Cont failureRead Y descentRead ->
              Cont descentRead N named ->
                PkgSig bundle named pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row named ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row O ∨ hsame row M ∨ hsame row Pi ∨
                        hsame row F ∨ hsame row Cn ∨ hsame row B ∨ hsame row Y ∨
                          hsame row named)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S F fitRead ∧
                        Cont fitRead Cn stabilityRead ∧
                          Cont stabilityRead B failureRead ∧
                            Cont failureRead Y descentRead ∧ PkgSig bundle named pkg)
                    hsame ∧ UnaryHistory fitRead ∧ UnaryHistory stabilityRead ∧
                      UnaryHistory failureRead ∧ UnaryHistory descentRead ∧
                        UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier fitRoute stabilityRoute failureRoute descentRoute namedRoute namedPkg
  obtain ⟨_fields, sourceUnary, _openUnary, _modelUnary, _probeUnary, fitUnaryBase,
    stabilityUnaryBase, failureUnaryBase, descentUnaryBase, _transportUnary,
    _replayUnary, _provenanceUnary, nameUnary, _namePkg⟩ := carrier
  have fitUnary : UnaryHistory fitRead :=
    unary_cont_closed sourceUnary fitUnaryBase fitRoute
  have stabilityUnary : UnaryHistory stabilityRead :=
    unary_cont_closed fitUnary stabilityUnaryBase stabilityRoute
  have failureUnary : UnaryHistory failureRead :=
    unary_cont_closed stabilityUnary failureUnaryBase failureRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed failureUnary descentUnaryBase descentRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed descentUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row named ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row O ∨ hsame row M ∨ hsame row Pi ∨ hsame row F ∨
            hsame row Cn ∨ hsame row B ∨ hsame row Y ∨ hsame row named)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S F fitRead ∧ Cont fitRead Cn stabilityRead ∧
            Cont stabilityRead B failureRead ∧ Cont failureRead Y descentRead ∧
              PkgSig bundle named pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        ⟨source.right, fitRoute, stabilityRoute, failureRoute, descentRoute, namedPkg⟩
  }
  exact ⟨cert, fitUnary, stabilityUnary, failureUnary, descentUnary, namedUnary⟩

end BEDC.Derived.PhysicalInductionGateUp
