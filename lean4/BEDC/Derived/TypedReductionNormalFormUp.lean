import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TypedReductionNormalFormUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TypedReductionNormalFormPacket [AskSetup] [PackageSetup]
    (term judgment membership reduction normal transport continuation provenance name endpoint : BHist)
    (mark : BMark) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory term ∧ UnaryHistory judgment ∧ UnaryHistory membership ∧
    UnaryHistory reduction ∧ UnaryHistory normal ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        UnaryHistory endpoint ∧ Ext term mark membership ∧ Cont membership reduction normal ∧
          Cont normal continuation endpoint ∧ hsame normal endpoint ∧
            hsame provenance endpoint ∧ hsame name endpoint ∧ PkgSig bundle endpoint pkg

theorem TypedReductionNormalFormPacket_namecert_obligations [AskSetup] [PackageSetup]
    {term judgment membership reduction normal transport continuation provenance name
      endpoint : BHist}
    {mark : BMark} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TypedReductionNormalFormPacket term judgment membership reduction normal transport
        continuation provenance name endpoint mark bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            TypedReductionNormalFormPacket term judgment membership reduction normal transport
              continuation provenance name endpoint mark bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row normal)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
          hsame ∧
        Ext term mark membership ∧ Cont membership reduction normal ∧
          Cont normal continuation endpoint := by
  -- BEDC touchpoint anchor: BHist Ext Cont hsame SemanticNameCert
  intro packet
  have packetWitness := packet
  obtain ⟨_termUnary, _judgmentUnary, _membershipUnary, _reductionUnary, _normalUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameUnary, _endpointUnary,
    membershipRow, reductionRow, endpointRow, normalSameEndpoint, provenanceSameEndpoint,
    _nameSameEndpoint, endpointPkg⟩ := packet
  have endpointSameNormal : hsame endpoint normal :=
    hsame_symm normalSameEndpoint
  have endpointSameProvenance : hsame endpoint provenance :=
    hsame_symm provenanceSameEndpoint
  have certCore :
      NameCert
        (fun row : BHist =>
          TypedReductionNormalFormPacket term judgment membership reduction normal transport
            continuation provenance name endpoint mark bundle pkg ∧ hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro packetWitness (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            TypedReductionNormalFormPacket term judgment membership reduction normal transport
              continuation provenance name endpoint mark bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row normal)
          (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row sourceRow
        exact hsame_trans sourceRow.right endpointSameNormal
      ledger_sound := by
        intro _row sourceRow
        exact And.intro (hsame_trans sourceRow.right endpointSameProvenance) endpointPkg
    }
  exact ⟨semantic, membershipRow, reductionRow, endpointRow⟩

end BEDC.Derived.TypedReductionNormalFormUp
