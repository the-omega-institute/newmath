import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_real_approximation_ledger_nonescape [AskSetup] [PackageSetup]
    {boundary adjacency mediant level tolerance stern density rational stream regular approx sealRow
      transport replay provenance name approxRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier boundary adjacency mediant level tolerance stern density rational stream
        regular approx sealRow transport replay provenance name bundle pkg ->
      Cont stream regular approxRead ->
        Cont approxRead sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row boundary ∨ hsame row adjacency ∨ hsame row mediant ∨
                      hsame row level ∨ hsame row tolerance ∨ hsame row stream ∨
                        hsame row regular ∨ hsame row approx ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont stream regular approxRead ∧
                      Cont approxRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
              UnaryHistory approxRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier approxRoute sealRoute sealPkg
  obtain ⟨_boundaryUnary, _adjacencyUnary, _mediantUnary, _levelUnary, _toleranceUnary,
    _sternUnary, _densityUnary, _rationalUnary, streamUnary, regularUnary, _approxUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _adjacencyEmpty,
    _sternEmpty, _mediantEmpty, _approxEmpty, _sealEmpty, _carrierPkg⟩ := carrier
  have approxReadUnary : UnaryHistory approxRead :=
    unary_cont_closed streamUnary regularUnary approxRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed approxReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundary ∨ hsame row adjacency ∨ hsame row mediant ∨
              hsame row level ∨ hsame row tolerance ∨ hsame row stream ∨
                hsame row regular ∨ hsame row approx ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream regular approxRead ∧
      Cont approxRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
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
                    (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, approxRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, approxReadUnary, sealReadUnary⟩

end BEDC.Derived.FareySequenceUp
