import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalTailMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofinalTailMapCarrier [AskSetup] [PackageSetup]
    (sourceWindow targetWindow sourceService targetService mapRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceWindow ∧ UnaryHistory targetWindow ∧ UnaryHistory sourceService ∧
    UnaryHistory targetService ∧ UnaryHistory mapRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont sourceWindow mapRow targetWindow ∧ Cont sourceService mapRow targetService ∧
          hsame transport localName ∧ PkgSig bundle provenance pkg

theorem CofinalTailMapCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I J U V M H C P N tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalTailMapCarrier I J U V M H C P N bundle pkg →
      Cont I M tailRead →
        PkgSig bundle tailRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row J ∨ hsame row U ∨ hsame row V ∨
                  hsame row M ∨ hsame row N ∨ hsame row tailRead)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle tailRead pkg ∧
                  (hsame row V ∨ hsame row tailRead))
              hsame ∧
            UnaryHistory tailRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro carrier sourceMapTail tailReadPkg
  obtain ⟨sourceWindowUnary, _targetWindowUnary, _sourceServiceUnary, _targetServiceUnary,
    mapRowUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _sourceMapTarget, _serviceMapTarget, _transportLocalName, provenancePkg⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceWindowUnary mapRowUnary sourceMapTail
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row U ∨ hsame row V ∨ hsame row M ∨
              hsame row N ∨ hsame row tailRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle tailRead pkg ∧
              (hsame row V ∨ hsame row tailRead))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro tailRead ⟨hsame_refl tailRead, tailReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, tailReadPkg, Or.inr source.left⟩
  }
  exact ⟨cert, tailReadUnary⟩

end BEDC.Derived.CofinalTailMapUp
