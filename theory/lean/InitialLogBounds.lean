import RealLogCertificate

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace AgentUCTRealIndex

theorem log_9_interval : ((4394449/2000000):ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ ((21972247/10000000):ℝ) := by
  apply dyadic_log_interval 9 ((7/16)) ((4394449/2000000)) ((21972247/10000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_10_interval : ((460517/200000):ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ ((23025851/10000000):ℝ) := by
  apply dyadic_log_interval 10 ((3/8)) ((460517/200000)) ((23025851/10000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_11_interval : ((2997369/1250000):ℝ) ≤ Real.log 11 ∧ Real.log 11 ≤ ((23978953/10000000):ℝ) := by
  apply dyadic_log_interval 11 ((5/16)) ((2997369/1250000)) ((23978953/10000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

theorem log_12_interval : ((12424533/5000000):ℝ) ≤ Real.log 12 ∧ Real.log 12 ≤ ((24849067/10000000):ℝ) := by
  apply dyadic_log_interval 12 ((1/4)) ((12424533/5000000)) ((24849067/10000000)) 4 20
  all_goals norm_num [logSeries,logRemainder,Finset.sum_range_succ]

end AgentUCTRealIndex
