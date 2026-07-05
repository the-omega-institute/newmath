import BEDC.Derived.NontrivialZeroClassifierUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NontrivialZeroClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NontrivialZeroClassifierCarrier
    (zero strip witness trivialLedger realPart rationalLedger transport replay provenance
      localName : BHist) : Prop :=
  UnaryHistory zero ∧ UnaryHistory strip ∧ UnaryHistory witness ∧
    UnaryHistory trivialLedger ∧ UnaryHistory realPart ∧ UnaryHistory rationalLedger ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName

theorem NontrivialZeroClassifierCarrier_route_certificate [AskSetup] [PackageSetup]
    {zero strip witness trivialLedger realPart rationalLedger transport replay provenance
      localName stripRead witnessRead trivialRead ledgerRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NontrivialZeroClassifierCarrier zero strip witness trivialLedger realPart rationalLedger
        transport replay provenance localName →
      Cont zero strip stripRead →
        Cont stripRead witness witnessRead →
          Cont trivialLedger realPart trivialRead →
            Cont trivialRead rationalLedger ledgerRead →
              Cont witnessRead ledgerRead consumerRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle localName pkg →
                    PkgSig bundle consumerRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row zero ∨ hsame row strip ∨ hsame row witness ∨
                              hsame row trivialLedger ∨ hsame row rationalLedger ∨
                                hsame row consumerRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont zero strip stripRead ∧
                              Cont stripRead witness witnessRead ∧
                                Cont trivialLedger realPart trivialRead ∧
                                  Cont trivialRead rationalLedger ledgerRead ∧
                                    Cont witnessRead ledgerRead consumerRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg ∧
                                          PkgSig bundle consumerRead pkg)
                          hsame ∧
                        UnaryHistory stripRead ∧ UnaryHistory witnessRead ∧
                          UnaryHistory trivialRead ∧ UnaryHistory ledgerRead ∧
                            UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame SemanticNameCert
  intro carrier stripRoute witnessRoute trivialRoute ledgerRoute consumerRoute provenancePkg
    localNamePkg consumerPkg
  have zeroUnary : UnaryHistory zero := carrier.left
  have stripUnary : UnaryHistory strip := carrier.right.left
  have witnessUnary : UnaryHistory witness := carrier.right.right.left
  have trivialLedgerUnary : UnaryHistory trivialLedger := carrier.right.right.right.left
  have realPartUnary : UnaryHistory realPart := carrier.right.right.right.right.left
  have rationalLedgerUnary : UnaryHistory rationalLedger :=
    carrier.right.right.right.right.right.left
  have stripReadUnary : UnaryHistory stripRead :=
    unary_cont_closed zeroUnary stripUnary stripRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed stripReadUnary witnessUnary witnessRoute
  have trivialReadUnary : UnaryHistory trivialRead :=
    unary_cont_closed trivialLedgerUnary realPartUnary trivialRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed trivialReadUnary rationalLedgerUnary ledgerRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed witnessReadUnary ledgerReadUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zero ∨ hsame row strip ∨ hsame row witness ∨
              hsame row trivialLedger ∨ hsame row rationalLedger ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont zero strip stripRead ∧
              Cont stripRead witness witnessRead ∧ Cont trivialLedger realPart trivialRead ∧
                Cont trivialRead rationalLedger ledgerRead ∧
                  Cont witnessRead ledgerRead consumerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, stripRoute, witnessRoute, trivialRoute, ledgerRoute,
          consumerRoute, provenancePkg, localNamePkg, consumerPkg⟩
  }
  exact
    ⟨cert, stripReadUnary, witnessReadUnary, trivialReadUnary, ledgerReadUnary,
      consumerReadUnary⟩

end BEDC.Derived.NontrivialZeroClassifierUp
