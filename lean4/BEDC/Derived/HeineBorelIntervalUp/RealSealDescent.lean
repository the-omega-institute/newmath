import BEDC.Derived.HeineBorelIntervalUp.TasteGate

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalRealSealDescent [AskSetup] [PackageSetup]
    (x : HeineBorelIntervalUp)
    {A B K M Z F T S R E Q C P N net mesh coverageRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    heineBorelIntervalFields x = [A, B, K, M, Z, F, T, S, R, E, Q, C, P, N] →
      HeineBorelIntervalCoverageRoute x net mesh coverageRead bundle pkg →
        UnaryHistory E →
          Cont coverageRead E sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row B ∨ hsame row K ∨ hsame row M ∨
                      hsame row Z ∨ hsame row F ∨ hsame row T ∨ hsame row S ∨
                        hsame row R ∨ hsame row E ∨ hsame row Q ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont coverageRead E sealRead ∧
                      PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields route eUnary sealRoute sealPkg
  cases x with
  | mk A' B' K' M' Z' F' T' S' R' E' Q' C' P' N' =>
      injection fields with hA htail
      injection htail with hB htail
      injection htail with hK htail
      injection htail with hM htail
      injection htail with hZ htail
      injection htail with hF htail
      injection htail with hT htail
      injection htail with hS htail
      injection htail with hR htail
      injection htail with hE htail
      injection htail with hQ htail
      injection htail with hC htail
      injection htail with hP htail
      injection htail with hN _
      subst hA
      subst hB
      subst hK
      subst hM
      subst hZ
      subst hF
      subst hT
      subst hS
      subst hR
      subst hE
      subst hQ
      subst hC
      subst hP
      subst hN
      have coverageResult :
          SemanticNameCert
              (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row net ∨ hsame row mesh ∨ hsame row coverageRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont net mesh coverageRead ∧
                  PkgSig bundle coverageRead pkg)
              hsame ∧
            UnaryHistory coverageRead :=
        HeineBorelIntervalNetCoverage
          (HeineBorelIntervalUp.mk A' B' K' M' Z' F' T' S' R' E' Q' C' P' N')
          route
      have coverageUnary : UnaryHistory coverageRead := coverageResult.right
      have sealUnary : UnaryHistory sealRead :=
        unary_cont_closed coverageUnary eUnary sealRoute
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row A' ∨ hsame row B' ∨ hsame row K' ∨ hsame row M' ∨
                  hsame row Z' ∨ hsame row F' ∨ hsame row T' ∨ hsame row S' ∨
                    hsame row R' ∨ hsame row E' ∨ hsame row Q' ∨ hsame row C' ∨
                      hsame row P' ∨ hsame row N' ∨ hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont coverageRead E' sealRead ∧
                  PkgSig bundle sealRead pkg)
              hsame := {
        core := {
          carrier_inhabited := Exists.intro sealRead
            ⟨hsame_refl sealRead, sealUnary⟩
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
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                Or.inr <| Or.inr source.left
        ledger_sound := by
          intro _row source
          exact ⟨source.right, sealRoute, sealPkg⟩
      }
      exact ⟨cert, sealUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
