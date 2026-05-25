import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SylowUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SylowCarrier [AskSetup] [PackageSetup]
    (groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  UnaryHistory groupRow ∧ UnaryHistory subgroupRow ∧ UnaryHistory primeRow ∧
    UnaryHistory exponentRow ∧ UnaryHistory coverageRow ∧ UnaryHistory actionRow ∧
      UnaryHistory transportRow ∧ UnaryHistory consumerRow ∧ UnaryHistory hsameRow ∧
        UnaryHistory provenance ∧ UnaryHistory localCert ∧
          Cont groupRow subgroupRow coverageRow ∧ Cont coverageRow actionRow transportRow ∧
            Cont transportRow consumerRow hsameRow ∧ hsame consumerRow provenance ∧
              hsame hsameRow provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localCert pkg

theorem SylowCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow consumerRow
      hsameRow provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                transportRow consumerRow hsameRow provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory groupRow ∧ UnaryHistory subgroupRow ∧ UnaryHistory primeRow ∧
          UnaryHistory exponentRow ∧ UnaryHistory coverageRow ∧ UnaryHistory actionRow ∧
            UnaryHistory transportRow ∧ UnaryHistory consumerRow ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier
  have carrierPacket :
      SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow transportRow
        consumerRow hsameRow provenance localCert bundle pkg :=
    carrier
  obtain ⟨groupUnary, subgroupUnary, primeUnary, exponentUnary, coverageUnary, actionUnary,
    transportUnary, consumerUnary, _hsameUnary, _provenanceUnary, _localCertUnary,
    _coverageRoute, _transportRoute, _consumerRoute, sameConsumerProvenance,
    _sameHsameProvenance, provenancePkg, _localCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row provenance ∧
              SylowCarrier groupRow subgroupRow primeRow exponentRow coverageRow actionRow
                transportRow consumerRow hsameRow provenance localCert bundle pkg)
          (fun row : BHist =>
            hsame row groupRow ∨ hsame row subgroupRow ∨ hsame row primeRow ∨
              hsame row exponentRow ∨ hsame row coverageRow ∨ hsame row actionRow ∨
                hsame row transportRow ∨ hsame row consumerRow)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
          hsame := by
    have consumerPattern :
        hsame provenance groupRow ∨ hsame provenance subgroupRow ∨
          hsame provenance primeRow ∨ hsame provenance exponentRow ∨
            hsame provenance coverageRow ∨ hsame provenance actionRow ∨
              hsame provenance transportRow ∨ hsame provenance consumerRow := by
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hsame_symm sameConsumerProvenance)))))))
    exact {
      core := {
        carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, carrierPacket⟩
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
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        cases sourceRow.left with
        | refl =>
            exact consumerPattern
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, provenancePkg⟩
    }
  exact
    ⟨cert, groupUnary, subgroupUnary, primeUnary, exponentUnary, coverageUnary, actionUnary,
      transportUnary, consumerUnary, provenancePkg⟩

end BEDC.Derived.SylowUp
