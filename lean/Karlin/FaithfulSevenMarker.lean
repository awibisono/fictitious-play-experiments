import Karlin.FaithfulSevenData

namespace Karlin.FaithfulSevenData
open scoped BigOperators
open FaithfulClock FaithfulWindow
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def coreCount (p n : ℕ) : Fin 6 → ℚ :=
  ![q_aux (21*((p:ℚ)+20)+10+n) 0 - q_aux (21*((p:ℚ)+20)+10) 0,
    q_aux (21*((p:ℚ)+20)+10+n) 1 - q_aux (21*((p:ℚ)+20)+10) 1,
    q_aux (21*((p:ℚ)+20)+10+n) 2 - q_aux (21*((p:ℚ)+20)+10) 2, 0, 0, 0]

theorem run_count (p v : ℕ) (i : Fin 6) :
    wordCountVec (run p v) i = if i = sevenPhaseAct p v then (sevenPhaseLen p v : ℚ) else 0 := by
  by_cases hi : i = sevenPhaseAct p v
  · subst i; simp [run, wordCountVec]
  · simp [run, wordCountVec, List.count_replicate, hi, Ne.symm hi]

theorem core_runs (p n : ℕ) (hn : n < 7*p+146) :
    run p (3*n) = List.replicate (6*(21*(p+20)+10+n)+1) (0:Fin 6) ∧
    run p (3*n+1) = List.replicate (6*(21*(p+20)+10+n)+3) (1:Fin 6) ∧
    run p (3*n+2) = List.replicate (6*(21*(p+20)+10+n)+5) (2:Fin 6) := by
  have h0 : 3*n < 21*p+438 := by omega
  have h1 : 3*n+1 < 21*p+438 := by omega
  have h2 : 3*n+2 < 21*p+438 := by omega
  have hd1 : (3*n+1)/3=n := by omega
  have hd2 : (3*n+2)/3=n := by omega
  simp [run, sevenPhaseLen, sevenPhaseAct, h0,h1,h2,hd1,hd2]

theorem runs_succ (p n : ℕ) : runs p (n+1) = runs p n ++ run p n := by
  simp [runs, consecutiveWord]

theorem runs_core_count (p n : ℕ) (hn : n ≤ 7*p+146) :
    wordCountVec (runs p (3*n)) = coreCount p n := by
  induction n with
  | zero => ext i; fin_cases i <;> simp [runs, consecutiveWord, coreCount, wordCountVec]
  | succ n ih =>
      have hn' : n < 7*p+146 := by omega
      have he : 3*(n+1)=((3*n+1)+1)+1 := by omega
      rw [he, runs_succ, runs_succ, runs_succ]
      rcases core_runs p n hn' with ⟨h0,h1,h2⟩
      rw [h0,h1,show 3*n+1+1=3*n+2 by omega,h2]
      ext i
      simp only [wordCountVec_append, ih (by omega)]
      fin_cases i <;>
        simp [coreCount, q_aux, wordCountVec, List.count_replicate] <;> ring

theorem coreCount_final (p : ℕ) : coreCount p (7*p+146) =
    ![Q_seven ((p:ℚ)+20) 0,Q_seven ((p:ℚ)+20) 1,Q_seven ((p:ℚ)+20) 2,0,0,0] := by
  ext i
  fin_cases i <;> simp [coreCount, q_aux, Q_seven] <;> ring

theorem guard_runs (p : ℕ) :
    run p (21*p+438) = List.replicate (882*p^2+32976*p+319218) (3:Fin 6) ∧
    run p (21*p+439) = List.replicate (882*p^2+37680*p+403222) (4:Fin 6) ∧
    run p (21*p+440) = List.replicate (882*p^2+21804*p+119722) (5:Fin 6) := by
  have h1 : 21*p+439 ≠ 21*p+438 := by omega
  have h2 : 21*p+440 ≠ 21*p+438 := by omega
  have h3 : 21*p+440 ≠ 21*p+439 := by omega
  have h4 : ¬21*p+439 < 21*p+438 := by omega
  have h5 : ¬21*p+440 < 21*p+438 := by omega
  simp [run, sevenPhaseLen, sevenPhaseAct, h4,h5]

theorem phase_counts (p : ℕ) : wordCountVec (phaseWord p) = QL_seven ((p:ℚ)+20) := by
  have he : sevenPhaseRunCount p = ((3*(7*p+146)+1)+1)+1 := by
    simp [sevenPhaseRunCount]; omega
  unfold phaseWord
  rw [he, runs_succ, runs_succ, runs_succ]
  have h0 : 3*(7*p+146) = 21*p+438 := by omega
  have h1 : 3*(7*p+146)+1 = 21*p+439 := by omega
  have h2 : 3*(7*p+146)+1+1 = 21*p+440 := by omega
  rcases guard_runs p with ⟨hg0,hg1,hg2⟩
  rw [show 3*(7*p+146)+1+1=3*(7*p+146)+2 by omega]
  rw [show 3*(7*p+146)+2=21*p+440 by omega,h1,h0,hg0,hg1,hg2,←h0]
  ext i
  simp only [wordCountVec_append, runs_core_count p (7*p+146) le_rfl, coreCount_final]
  fin_cases i <;>
    simp [wordCountVec, List.count_replicate, QL_seven, L_seven] <;> ring

theorem seven_counts (q : ℕ) (hq : 20 ≤ q) :
    wordCountVec (sevenWord q) = (ratCount CInteger).mulVec (binomBasis 3 q) := by
  rw [ratCount_CInteger, C_eval, sevenWord, phase_counts]
  congr 1
  rw [Nat.cast_sub hq]
  norm_num


theorem dot_replicate (v : Fin 6 → ℚ) (a : Fin 6) (h : ℕ) :
    dotProduct v (wordCountVec (List.replicate h a)) = (h:ℚ)*v a := by
  classical
  simp only [dotProduct, wordCountVec, List.count_replicate]
  simp [mul_comm]

theorem core_counter_formula (p n : ℕ) :
    dotProduct v_seven (coreCount p n) =
      (n:ℚ)*(588-6*(21*((p:ℚ)+20)+10)-3*n)/17641 := by
  simp [dotProduct, Fin.sum_univ_six, v_seven, coreCount, q_aux]
  ring

theorem core_counter_nonpos (p n : ℕ) : dotProduct v_seven (coreCount p n) ≤ 0 := by
  rw [core_counter_formula]
  have hp : 0 ≤ (p:ℚ) := Nat.cast_nonneg p
  have hn : 0 ≤ (n:ℚ) := Nat.cast_nonneg n
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos hn (by linarith)
  · norm_num

theorem core_prefix_counter (p v h : ℕ) (hv : v < 21*p+438)
    (hh : h < sevenPhaseLen p v) :
    dotProduct v_seven (wordCountVec (runs p v ++
      List.replicate h (sevenPhaseAct p v))) ≤ 0 := by
  let n := v/3
  have hn : n < 7*p+146 := by dsimp [n]; omega
  have hmod : v%3=0 ∨ v%3=1 ∨ v%3=2 := by omega
  rcases core_runs p n hn with ⟨h0,h1,h2⟩
  rcases hmod with hm | hm | hm
  · have he : v=3*n := by dsimp [n]; omega
    have ha : sevenPhaseAct p v=0 := by simp [sevenPhaseAct,hv,hm]
    rw [dotCount_append, ha, dot_replicate, v_seven, mul_zero, add_zero, he,
      runs_core_count p n hn.le]
    exact core_counter_nonpos p n
  · have he : v=3*n+1 := by dsimp [n]; omega
    have ha : sevenPhaseAct p v=1 := by simp [sevenPhaseAct,hv,hm]
    rw [dotCount_append, ha, dot_replicate, he, runs_succ, h0,
      dotCount_append, runs_core_count p n hn.le, dot_replicate]
    norm_num [v_seven]
    have hc := core_counter_nonpos p n
    have hh0 : 0 ≤ (h:ℚ) := Nat.cast_nonneg h
    linarith
  · have he : v=3*n+2 := by dsimp [n]; omega
    have ha : sevenPhaseAct p v=2 := by simp [sevenPhaseAct,hv,hm]
    have hd : v/3=n := rfl
    have hlen : sevenPhaseLen p v=6*(21*(p+20)+10+n)+5 := by
      simp [sevenPhaseLen,hv,hm,hd]
    have hhQ : (h:ℚ) ≤ 6*(21*((p:ℚ)+20)+10+n)+5 := by
      have := (Nat.cast_le (α:=ℚ)).mpr (Nat.le_of_lt hh)
      rw [hlen] at this
      push_cast at this
      exact this
    rw [dotCount_append,ha,dot_replicate,he,
      show 3*n+2=(3*n+1)+1 by omega,runs_succ,runs_succ,h0,h1,
      dotCount_append,dotCount_append,runs_core_count p n hn.le,dot_replicate,dot_replicate]
    rw [core_counter_formula]
    norm_num [v_seven]
    have hc := core_counter_nonpos p (n+1)
    rw [core_counter_formula] at hc
    push_cast at hc
    nlinarith

theorem phase_counter (p : ℕ) : dotProduct v_seven (wordCountVec (phaseWord p)) = 1 := by
  rw [phase_counts]
  simp [dotProduct, Fin.sum_univ_six, v_seven, QL_seven, Q_seven, L_seven]
  ring

theorem guard_prefix_counter (p : ℕ) :
    dotProduct v_seven (wordCountVec (runs p (21*p+438))) =
      1 - (7/105846:ℚ)*L_seven ((p:ℚ)+20) 0 ∧
    dotProduct v_seven (wordCountVec (runs p (21*p+439))) = 1 ∧
    dotProduct v_seven (wordCountVec (runs p (21*p+440))) = 1 := by
  have hc : 21*p+438=3*(7*p+146) := by omega
  have he1 : 21*p+439=(21*p+438)+1 := by omega
  have he2 : 21*p+440=(21*p+439)+1 := by omega
  rcases guard_runs p with ⟨hg0,hg1,hg2⟩
  have h0 : dotProduct v_seven (wordCountVec (runs p (21*p+438))) =
      1-(7/105846:ℚ)*L_seven ((p:ℚ)+20) 0 := by
    rw [hc,runs_core_count p (7*p+146) le_rfl,core_counter_formula]
    simp [L_seven]
    ring
  refine ⟨h0, ?_, ?_⟩
  · rw [he1,runs_succ,dotCount_append,h0,hg0,dot_replicate]
    simp [v_seven,L_seven]
    ring
  · rw [he2,runs_succ,dotCount_append,he1,runs_succ,dotCount_append,h0,hg0,hg1,
      dot_replicate,dot_replicate]
    simp [v_seven,L_seven]
    ring


theorem guard_gap1 (q h : ℚ) :
    (stateBeforeG1 q 3 + M_seven 3 3*h) -
      (stateBeforeG1 q 0 + M_seven 0 3*h) = 1/200+h/84 := by
  simp [stateBeforeG1,V_seven,W_seven,Vg_seven,H_seven,s_seven,
    Fin.sum_univ_three,M_seven,G_seven,Q_seven,A_guard,L_seven]
  ring

theorem guard_gap2 (q h : ℚ) :
    (stateBeforeG2 q 4 + M_seven 4 4*h) -
      (stateBeforeG2 q 0 + M_seven 0 4*h) =
      19/2268*(L_seven q 1-h)+2/567*L_seven q 2+1/25-1/21 := by
  simp [stateBeforeG2,stateBeforeG1,V_seven,W_seven,Vg_seven,H_seven,s_seven,
    Fin.sum_univ_three,M_seven,G_seven,Q_seven,A_guard,L_seven]
  ring

theorem guard_gap3 (q h : ℚ) :
    (stateBeforeG3 q 5 + M_seven 5 5*h) -
      (stateBeforeG3 q 0 + M_seven 0 5*h) =
      2/567*(L_seven q 2-h)-1/2000 := by
  simp [stateBeforeG3,stateBeforeG2,stateBeforeG1,V_seven,W_seven,Vg_seven,
    H_seven,s_seven,Fin.sum_univ_three,M_seven,G_seven,Q_seven,A_guard,L_seven]
  ring

theorem run_marker (p v h : ℕ) (hv : v < sevenPhaseRunCount p)
    (hh : h < sevenPhaseLen p v) :
    (3433/1134000:ℚ) ≤
      height (0:Fin 6) (wordScore M_seven (sevenPhaseScore p v)
        (List.replicate h (sevenPhaseAct p v))) -
      wordScore M_seven (sevenPhaseScore p v) (List.replicate h (sevenPhaseAct p v)) 0 +
      1-dotProduct v_seven (wordCountVec (runs p v))-(h:ℚ)*v_seven (sevenPhaseAct p v) := by
  have hq : (20:ℚ) ≤ (p:ℚ)+20 := by linarith [Nat.cast_nonneg (α:=ℚ) p]
  have hh0 : (0:ℚ) ≤ h := Nat.cast_nonneg h
  by_cases hc : v < 21*p+438
  · have hp := core_prefix_counter p v h hc hh
    rw [dotCount_append,dot_replicate] at hp
    have hm := le_height (0:Fin 6) (wordScore M_seven (sevenPhaseScore p v)
      (List.replicate h (sevenPhaseAct p v))) 0
    linarith
  · have hv' : v=21*p+438 ∨ v=21*p+439 ∨ v=21*p+440 := by
      unfold sevenPhaseRunCount at hv
      omega
    rcases guard_prefix_counter p with ⟨hc0,hc1,hc2⟩
    rcases hv' with rfl | rfl | rfl
    · have ha : sevenPhaseAct p (21*p+438)=3 := by simp [sevenPhaseAct]
      have hs : sevenPhaseScore p (21*p+438)=stateBeforeG1 ((p:ℚ)+20) := by
        simp [sevenPhaseScore]
      rw [ha,hs,hc0]
      have hm := le_height (0:Fin 6)
        (wordScore M_seven (stateBeforeG1 ((p:ℚ)+20)) (List.replicate h 3)) 3
      rw [wordScore_replicate] at hm
      rw [wordScore_replicate]
      have hg := guard_gap1 ((p:ℚ)+20) h
      have hL := (seven_run_lengths_lower_bound hq).2.2.2.1
      norm_num [v_seven] at *
      nlinarith
    · have h1 : 21*p+439 ≠ 21*p+438 := by omega
      have ha : sevenPhaseAct p (21*p+439)=4 := by simp [sevenPhaseAct]
      have hs : sevenPhaseScore p (21*p+439)=stateBeforeG2 ((p:ℚ)+20) := by
        simp [sevenPhaseScore]
      have hlen : (sevenPhaseLen p (21*p+439):ℚ)=L_seven ((p:ℚ)+20) 1 := by
        simp [sevenPhaseLen,L_seven]
        ring
      have hhQ : (h:ℚ) ≤ L_seven ((p:ℚ)+20) 1-1 := by
        have := (Nat.cast_le (α:=ℚ)).mpr (Nat.succ_le_of_lt hh)
        push_cast at this
        rw [hlen] at this
        linarith
      rw [ha,hs,hc1]
      have hm := le_height (0:Fin 6)
        (wordScore M_seven (stateBeforeG2 ((p:ℚ)+20)) (List.replicate h 4)) 4
      rw [wordScore_replicate] at hm
      rw [wordScore_replicate]
      have hg := guard_gap2 ((p:ℚ)+20) h
      have hL := (seven_run_lengths_lower_bound hq).2.2.2.2.2.2
      norm_num [v_seven] at *
      linarith
    · have h1 : 21*p+440 ≠ 21*p+438 := by omega
      have h2 : 21*p+440 ≠ 21*p+439 := by omega
      have ha : sevenPhaseAct p (21*p+440)=5 := by simp [sevenPhaseAct]
      have hs : sevenPhaseScore p (21*p+440)=stateBeforeG3 ((p:ℚ)+20) := by
        simp [sevenPhaseScore]
      have hlen : (sevenPhaseLen p (21*p+440):ℚ)=L_seven ((p:ℚ)+20) 2 := by
        simp [sevenPhaseLen,L_seven]
        ring
      have hhQ : (h:ℚ) ≤ L_seven ((p:ℚ)+20) 2-1 := by
        have := (Nat.cast_le (α:=ℚ)).mpr (Nat.succ_le_of_lt hh)
        push_cast at this
        rw [hlen] at this
        linarith
      rw [ha,hs,hc2]
      have hm := le_height (0:Fin 6)
        (wordScore M_seven (stateBeforeG3 ((p:ℚ)+20)) (List.replicate h 5)) 5
      rw [wordScore_replicate] at hm
      rw [wordScore_replicate]
      have hg := guard_gap3 ((p:ℚ)+20) h
      norm_num [v_seven] at *
      linarith

theorem phase_marker (p r : ℕ) (hr : r < (phaseWord p).length) :
    (3433/1134000:ℚ) ≤
      height (0:Fin 6) (wordScore M_seven (V_seven ((p:ℚ)+20)) ((phaseWord p).take r)) -
      wordScore M_seven (V_seven ((p:ℚ)+20)) ((phaseWord p).take r) 0 +
      dotProduct v_seven (wordCountVec ((phaseWord p).drop r)) := by
  obtain ⟨v,hv,h,hh,_,ht⟩ := consecutiveWord_prefix (run p) 0 (sevenPhaseRunCount p) r hr
  simp only [zero_add] at hh ht
  have hh' : h < sevenPhaseLen p v := by simpa [run] using hh
  have ht' : (phaseWord p).take r = runs p v ++ List.replicate h (sevenPhaseAct p v) := by
    simpa only [runs,run,List.take_replicate,Nat.min_eq_left hh'.le] using ht
  have hs : wordScore M_seven (V_seven ((p:ℚ)+20)) ((phaseWord p).take r) =
      wordScore M_seven (sevenPhaseScore p v) (List.replicate h (sevenPhaseAct p v)) := by
    rw [ht',wordScore_append,runs_score p v hv.le]
  have hd := dotCount_take_add_drop v_seven (phaseWord p) r
  rw [phase_counter,ht',dotCount_append,dot_replicate] at hd
  rw [hs]
  have hm := run_marker p v h hv hh'
  linarith

theorem seven_marker (q : ℕ) (hq : 20 ≤ q) (r : ℕ)
    (hr : r < (sevenWord q).length) :
    (3433/1134000:ℚ) ≤
      height (0:Fin 6) (wordScore M_seven (R_seven.mulVec (binomBasis 3 q)) ((sevenWord q).take r)) -
      wordScore M_seven (R_seven.mulVec (binomBasis 3 q)) ((sevenWord q).take r) 0 +
      dotProduct v_seven (wordCountVec ((sevenWord q).drop r)) := by
  rw [R_eval]
  have he : ((q-20:ℕ):ℚ)+20=(q:ℚ) := by rw [Nat.cast_sub hq]; norm_num
  simpa only [sevenWord,he] using phase_marker (q-20) r hr

end Karlin.FaithfulSevenData
