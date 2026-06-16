import BEDC.Derived.AnalogyCertificateGateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AnalogyCertificateGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AnalogyCertificateGateCarrier [AskSetup] [PackageSetup]
    (S K G R V U L E F H C P N : BHist)
    (_bundle : ProbeBundle ProbeName) (_pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  UnaryHistory S ∧
    UnaryHistory K ∧
      UnaryHistory G ∧
        UnaryHistory R ∧
          UnaryHistory V ∧
            UnaryHistory U ∧
              UnaryHistory L ∧
                UnaryHistory E ∧
                  UnaryHistory F ∧
                    UnaryHistory H ∧
                      UnaryHistory C ∧
                        UnaryHistory P ∧
                          UnaryHistory N ∧
                            Cont V U L ∧
                              Cont L E F

theorem AnalogyCertificateGateNameCertObligations [AskSetup] [PackageSetup]
    {S K G R V U L E F H C P N sameSchemaRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory K →
        UnaryHistory G →
          UnaryHistory R →
            UnaryHistory V →
              UnaryHistory U →
                UnaryHistory L →
                  UnaryHistory E →
                    UnaryHistory F →
                      UnaryHistory H →
                        UnaryHistory C →
                          UnaryHistory P →
                            UnaryHistory N →
                              Cont V U sameSchemaRead →
                                Cont L E ledgerRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                        (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row S ∨ hsame row K ∨ hsame row G ∨
                                            hsame row R ∨ hsame row V ∨ hsame row U ∨
                                              hsame row L ∨ hsame row E ∨ hsame row F ∨
                                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                  hsame row N ∨ hsame row sameSchemaRead ∨
                                                    hsame row ledgerRead)
                                        (fun row : BHist =>
                                          hsame row N ∧ Cont V U sameSchemaRead ∧
                                            Cont L E ledgerRead ∧ PkgSig bundle P pkg ∧
                                              PkgSig bundle N pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _sUnary _kUnary _gUnary _rUnary _vUnary _uUnary _lUnary _eUnary _fUnary
    _hUnary _cUnary _pUnary nUnary sameSchemaCont ledgerCont provenancePkg namePkg
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, nUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameSchemaCont, ledgerCont, provenancePkg, namePkg⟩
  }

theorem AnalogyCertificateGateCarrier_falsifiable_prediction [AskSetup] [PackageSetup]
    {S K G R V U L E F H C P N exactRead failureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AnalogyCertificateGateCarrier S K G R V U L E F H C P N bundle pkg →
      Cont V U L →
        Cont L E exactRead →
          Cont exactRead F failureRead →
            SemanticNameCert
                (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨
                    hsame row F ∨ hsame row exactRead ∨ hsame row failureRead)
                (fun row : BHist =>
                  hsame row exactRead ∧ Cont V U L ∧ Cont L E exactRead)
                hsame ∧ UnaryHistory exactRead ∧ UnaryHistory failureRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory ProbeBundle Pkg
  intro carrier routeVU routeExact routeFailure
  have vUnary : UnaryHistory V := carrier.right.right.right.right.left
  have uUnary : UnaryHistory U := carrier.right.right.right.right.right.left
  have lUnary : UnaryHistory L := carrier.right.right.right.right.right.right.left
  have eUnary : UnaryHistory E := carrier.right.right.right.right.right.right.right.left
  have fUnary : UnaryHistory F := carrier.right.right.right.right.right.right.right.right.left
  have exactUnary : UnaryHistory exactRead := by
    cases routeExact
    exact unary_append_closed lUnary eUnary
  have failureUnary : UnaryHistory failureRead := by
    cases routeFailure
    exact unary_append_closed exactUnary fUnary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row U ∨ hsame row L ∨ hsame row E ∨
              hsame row F ∨ hsame row exactRead ∨ hsame row failureRead)
          (fun row : BHist =>
            hsame row exactRead ∧ Cont V U L ∧ Cont L E exactRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro exactRead ⟨hsame_refl exactRead, exactUnary⟩
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
                    (Or.inl source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, routeVU, routeExact⟩
    }
  exact ⟨cert, exactUnary, failureUnary⟩

end BEDC.Derived.AnalogyCertificateGateUp
