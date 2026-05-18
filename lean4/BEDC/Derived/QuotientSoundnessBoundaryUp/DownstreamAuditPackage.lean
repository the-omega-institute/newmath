import BEDC.Derived.QuotientSoundnessBoundaryUp

namespace BEDC.Derived.QuotientSoundnessBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuotientSoundnessBoundaryDownstreamAuditPackage [AskSetup] [PackageSetup]
    {E A T V H C P N auditRead downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuotientSoundnessBoundaryCarrier E A T V H C P N bundle pkg →
      Cont E T H →
        Cont H C auditRead →
          Cont auditRead N downstreamRead →
            PkgSig bundle downstreamRead pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont E T H ∧ Cont H C auditRead ∧ Cont auditRead N downstreamRead ∧
                        hsame H N)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ PkgSig bundle downstreamRead pkg ∧
                        hsame row downstreamRead)
                    hsame ∧
                UnaryHistory auditRead ∧ UnaryHistory downstreamRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier eTransport hAudit auditDownstream downstreamPkg
  obtain ⟨_eUnary, _aUnary, _tUnary, _vUnary, hUnary, cUnary, _pUnary, nUnary,
    _eAV, _eTH, _hCN, pPkg, _nPkg, hSameN⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed hUnary cUnary hAudit
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed auditUnary nUnary auditDownstream
  have sourceWitness :
      hsame downstreamRead downstreamRead ∧ UnaryHistory downstreamRead :=
    ⟨hsame_refl downstreamRead, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstreamRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont E T H ∧ Cont H C auditRead ∧ Cont auditRead N downstreamRead ∧ hsame H N)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle downstreamRead pkg ∧
              hsame row downstreamRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstreamRead sourceWitness
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
      intro _row _source
      exact ⟨eTransport, hAudit, auditDownstream, hSameN⟩
    ledger_sound := by
      intro _row source
      exact ⟨pPkg, downstreamPkg, source.left⟩
  }
  exact ⟨cert, auditUnary, downstreamUnary⟩

end BEDC.Derived.QuotientSoundnessBoundaryUp
