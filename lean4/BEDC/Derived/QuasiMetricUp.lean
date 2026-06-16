import BEDC.Derived.QuasiMetricUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.QuasiMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuasiMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source point distance diagonal triangle ball filter net uniform transport replay provenance
      localName directedRead ballRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuasiMetricCarrier source point distance diagonal triangle ball filter net uniform transport
        replay provenance localName bundle pkg →
      Cont distance point directedRead →
        Cont directedRead ball ballRead →
          PkgSig bundle ballRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row ballRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row point ∨ hsame row distance ∨
                    hsame row diagonal ∨ hsame row triangle ∨ hsame row ball ∨
                      hsame row ballRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont distance point directedRead ∧
                    Cont directedRead ball ballRead ∧ PkgSig bundle ballRead pkg)
                hsame ∧
              UnaryHistory directedRead ∧ UnaryHistory ballRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier distancePointRead directedBallRead ballPkg
  obtain ⟨sourceUnary, pointUnary, diagonalUnary, ballUnary, _uniformUnary, _transportUnary,
    sourcePointDistance, distanceDiagonalTriangle, _triangleBallFilter, _ballUniformNet,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed sourceUnary pointUnary sourcePointDistance
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed distanceUnary pointUnary distancePointRead
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed directedUnary ballUnary directedBallRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ballRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row point ∨ hsame row distance ∨
              hsame row diagonal ∨ hsame row triangle ∨ hsame row ball ∨ hsame row ballRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont distance point directedRead ∧
              Cont directedRead ball ballRead ∧ PkgSig bundle ballRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ballRead ⟨hsame_refl ballRead, ballReadUnary⟩
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
      exact ⟨source.right, distancePointRead, directedBallRead, ballPkg⟩
  }
  exact ⟨cert, directedUnary, ballReadUnary⟩

theorem QuasiMetricCarrier_nonescape [AskSetup] [PackageSetup]
    {source points distance zero triangle ball filter net uniformReflection transport replay
      provenance localName ballRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuasiMetricCarrier source points distance zero triangle ball filter net uniformReflection
        transport replay provenance localName bundle pkg →
      Cont triangle ball ballRead →
        Cont ball uniformReflection completionRead →
          PkgSig bundle completionRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row distance ∨ hsame row triangle ∨ hsame row ball ∨
                    hsame row filter ∨ hsame row net ∨ hsame row uniformReflection ∨
                      hsame row completionRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont triangle ball ballRead ∧
                    Cont ball uniformReflection completionRead ∧
                      PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory distance ∧ UnaryHistory triangle ∧ UnaryHistory ballRead ∧
                UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier triangleBallRead ballUniformRead completionPkg
  obtain ⟨sourceUnary, pointUnary, zeroUnary, ballUnary, uniformUnary, _transportUnary,
    sourcePointDistance, distanceZeroTriangle, _triangleBallFilter, _ballUniformNet,
    _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed sourceUnary pointUnary sourcePointDistance
  have triangleUnary : UnaryHistory triangle :=
    unary_cont_closed distanceUnary zeroUnary distanceZeroTriangle
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed triangleUnary ballUnary triangleBallRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed ballUnary uniformUnary ballUniformRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row triangle ∨ hsame row ball ∨ hsame row filter ∨
              hsame row net ∨ hsame row uniformReflection ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont triangle ball ballRead ∧
              Cont ball uniformReflection completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact ⟨source.right, triangleBallRead, ballUniformRead, completionPkg⟩
  }
  exact ⟨cert, distanceUnary, triangleUnary, ballReadUnary, completionReadUnary⟩

end BEDC.Derived.QuasiMetricUp
