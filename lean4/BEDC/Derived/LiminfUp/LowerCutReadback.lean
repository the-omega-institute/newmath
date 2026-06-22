import BEDC.Derived.LiminfUp

namespace BEDC.Derived.LiminfUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LiminfLowerCutReadback [AskSetup] [PackageSetup]
    {sequence lowerCut dyadic upperSurface terminal transport replay provenance localName
      sealRead lowerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LiminfCarrier sequence lowerCut dyadic terminal transport replay provenance localName
        bundle pkg →
      UnaryHistory upperSurface →
      Cont lowerCut upperSurface dyadic →
      Cont terminal transport sealRead →
      Cont lowerCut dyadic lowerRead →
      PkgSig bundle provenance pkg →
      PkgSig bundle sealRead pkg →
      SemanticNameCert
          (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperSurface ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead ∨
                hsame row lowerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
              Cont lowerCut upperSurface dyadic ∧ Cont terminal transport sealRead ∧
                Cont lowerCut dyadic lowerRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame ∧
        UnaryHistory lowerRead := by
  -- BEDC touchpoint anchor: LiminfCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier _upperSurfaceUnary lowerUpperDyadic terminalTransport lowerDyadicRead
    provenancePkg sealPkg
  have sequenceUnary : UnaryHistory sequence := carrier.left
  have lowerCutUnary : UnaryHistory lowerCut := carrier.right.left
  have dyadicUnary : UnaryHistory dyadic := carrier.right.right.left
  have lowerReadUnary : UnaryHistory lowerRead :=
    unary_cont_closed lowerCutUnary dyadicUnary lowerDyadicRead
  have sequenceLowerDyadic : Cont sequence lowerCut dyadic :=
    carrier.right.right.right.right.right.right.right.right.left
  have sourceLowerRead :
      (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row) lowerRead := by
    exact ⟨hsame_refl lowerRead, lowerReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lowerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sequence ∨ hsame row lowerCut ∨ hsame row upperSurface ∨
              hsame row dyadic ∨ hsame row terminal ∨ hsame row sealRead ∨
                hsame row lowerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sequence lowerCut dyadic ∧
              Cont lowerCut upperSurface dyadic ∧ Cont terminal transport sealRead ∧
                Cont lowerCut dyadic lowerRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro lowerRead sourceLowerRead
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, sequenceLowerDyadic, lowerUpperDyadic, terminalTransport,
            lowerDyadicRead, provenancePkg, sealPkg⟩
    }
  exact ⟨cert, lowerReadUnary⟩

end BEDC.Derived.LiminfUp
