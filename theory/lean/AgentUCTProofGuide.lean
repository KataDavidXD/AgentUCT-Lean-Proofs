import AgentUCTPaper

/-!
# AgentUCT 中文 Lean 证明导读

这里按依赖顺序导航现有证明。每个 `#check` 解析真实声明，显示完整参数、假设和结论；
它本身不新增定理。具体证明体在对应模块，README第6节的E1–E4、Q1–Q9与这里对应。

Lean习惯：先读 `theorem ... (h...) : 结论`，再读 `:= by`。
`intro` 固定任意对象；`obtain` 拆存在/合取；`have` 命名中间目标；
`calc` 串联推导；`rw` 用已证恒等式替换；`apply` 拆为充分条件。
`linarith`、`nlinarith`、`omega` 完成已列前提上的线性、非线性、自然数算术。
数学假设不因tactic成功而获得实证验证。

## 0. 对象、假设、量词
TreeEvaluation只描述完整反馈；expanded是树节点，terminal是rollout完成路径。
LegalTreeRun给展开约束，选择最大性另由TreeAllocationRule给出。
FixedTableEvents使每次return等于固定表的值；PersistentCaches区分可恢复与已发布资源。
主定理先取实例级正gap下界，再量化所有合法有限历史与horizon。
-/
#check AgentUCTPaper.TreeEvaluation
#check AgentUCTPaper.LegalTreeRun
#check AgentUCTPaper.TreeAllocationRule
#check AgentUCTPaper.FixedTableEvents
#check AgentUCTPaper.PersistentCaches
#check AgentUCTPaper.BoundedTreeRun

/-! ## E1–E3. 真实回传 → 均值亏损恒等式 → 父亏损分解
对event列表归纳得到N与S；除正N得均值。D=N*V-S给Q=V-D/N。
终局反链与固定表使终局D=0。父事件按birth/下一child分组；birth≤1，根无birth。
局部动作流对应全局历史；父计数有根0、非根1的固定偏移。
-/
#check AgentUCTPaper.replayBackup_visits
#check AgentUCTPaper.replayBackup_rewardSum
#check AgentUCTPaper.replayBackup_mean
#check AgentUCTPaper.backedDeficit_identity
#check AgentUCTPaper.operational_mean_deficit
#check AgentUCTPaper.operational_mean_le_subtreeValue
#check AgentUCTPaper.terminal_backedDeficit_zero
#check AgentUCTPaper.operational_subtree_deficit_decomposition
#check AgentUCTPaper.internal_birthDeficit_le_one
#check AgentUCTPaper.root_birthDeficit_zero
#check AgentUCTPaper.localBefore_parent_count
#check AgentUCTPaper.projected_index_max

/-! ## E4. 执行冷账与checkpoint后缀
旧缓存与新增资源不交；并集记账逐项相消。前缀完整时，缺失集合恰是最深checkpoint后缀。
rollout可发布未展开前缀，该节点的树统计不随之更新。
-/
#check AgentUCTPaper.coldWork_sequential_union
#check AgentUCTPaper.replayMetered_cold_conservation
#check AgentUCTPaper.coldWork_eq_deepest_suffix
#check AgentUCTPaper.rollout_publication_without_backup

/-! ## Q1. 固定包络
需求包含于有限资源并集；law非负归一化。在线价格≤base，因此penalty≤H。
H不作为实际收费或调用准入界。
-/
#check AgentUCTPaper.referenceColdCost_bounded
#check AgentUCTPaper.coldForecastPenalty_bounded
#check AgentUCTPaper.completion_prediction_envelope

/-! ## Q2. 有限探索窗口
未访问优先完成初始化。反设目标child≤m→其bonus>H+2→被选child bonus>1。
选择前次数受log界；按child计数上界之和<窗口长度，矛盾。
显式L同时满足指数压力与平方长度条件；均值和罚项可有界自适应变化。
-/
#check AgentUCTPaper.initialized_after_unvisited_first
#check AgentUCTPaper.selected_count_under_pressure
#check AgentUCTPaper.small_count_window_bound
#check AgentUCTPaper.finite_window_explores
#check AgentUCTPaper.explorationWindowStart
#check AgentUCTPaper.explorationWindow_pressure
#check AgentUCTPaper.explorationWindow_long_enough
#check AgentUCTPaper.finite_explicit_window_explores
#check AgentUCTPaper.actual_children_explored

/-! ## Q3–Q4. 终局覆盖 → 可恢复资源覆盖 → 零冷罚项
剩余深度归纳：去掉一次birth，局部窗口给各child足够访问，再递归。
终局观察发布全panel-prefix资源；持久保留后missing为空，所有冷罚项为零。
仅有penalty有界不能跳过这一步。
-/
#check AgentUCTPaper.coverageVisits
#check AgentUCTPaper.actual_subtree_coverage
#check AgentUCTPaper.actual_terminal_coverage
#check AgentUCTPaper.actual_restorable_coverage
#check AgentUCTPaper.referenceColdCost_zero
#check AgentUCTPaper.coldForecastPenalty_after_coverage

/-! ## Q5–Q6. 子树偏差小 → 正gap child晚期选择受限
固定统一delta>0；显式m使孩子D/N≤delta/4，故最优child均值≥父最优值-delta/4。
burnin同时保证覆盖和足够访问；去除双方零罚项后，最大性迫使次优child bonus≥delta/2。
平方并清正分母给选择前次数界；加早期burnin和最后一次更新。
-/
#check AgentUCTPaper.finite_tree_positive_edge_gap
#check AgentUCTPaper.biasVisitTarget
#check AgentUCTPaper.logarithmic_deficit_small
#check AgentUCTPaper.selected_count_from_subtree_bias
#check AgentUCTPaper.count_le_burnin_add_cap
#check AgentUCTPaper.actual_suboptimal_child_count

/-! ## Q7–Q8. 剩余深度归纳 → 根累计质量界
终局D=0；父分解中正gap用次数界，零gap的N*gap=0，孩子用归纳界，birth≤1。
归纳同时量化全部历史前缀；根N=完整评估数，D=固定训练质量累计regret。
固定价格、共享缓存和被完整冷费用支配的非负罚项各有对应推论。
uniform_root表示跨合法历史统一常数，不要求均匀rollout。
-/
#check AgentUCTPaper.treeRateConstants
#check AgentUCTPaper.parent_deficit_log_bound
#check AgentUCTPaper.actual_subtree_log_deficit
#check AgentUCTPaper.root_count_eq_length
#check AgentUCTPaper.root_deficit_is_terminal_quality_regret
#check AgentUCTPaper.cold_forecast_uniform_root_log_bound
#check AgentUCTPaper.shared_cache_uniform_root_log_bound
#check AgentUCTPaper.dominated_cold_shared_root_log_bound
#check AgentUCTPaper.checkpoint_conditioned_shared_root_log_bound

/-! ## Q9. 在线均价和有限样本
prior与预测样本≤cap→正分母均值≤cap。样本按Fin n索引，重复完成保留质量。
交换有限和得样本均值，n>0得质量1；均价包络接历史价格定理。
law的归一化仍需独立前提；本链不证明MC准确性或真实固定reward。
-/
#check AgentUCTPaper.onlineMean_envelope
#check AgentUCTPaper.sampledLaw_expectation
#check AgentUCTPaper.sampledLaw_mass
#check AgentUCTPaper.onlineMean_completion_envelope
#check AgentUCTPaper.online_mean_shared_root_log_bound

/-! ## L. 同状态交换与误差证书
普通最大性→指数损失≥0；定价最大性→损失≤gamma*预测节省。
gamma>0→预测费用更低；拆两候选abs误差给条件费用节省下界。
质量误差还须另控制才有真实净收益证书；指定law的均值目标不认证经验law。
-/
#check AgentUCTPaper.priced_choice_tradeoff
#check AgentUCTPaper.physical_saving_certificate
#check AgentUCTPaper.actual_net_gain_certificate
#check AgentUCTPaper.referenceColdCost_resource_form
#check AgentUCTPaper.full_reference_cost_error
#check AgentUCTPaper.full_cost_mean_unique_mse_minimizer
#check AgentUCTPaper.selected_net_gap_from_cost_radii

/-! ## N. Next、各自轨迹、事后预算、最终推荐
旧nextEdgePenalty直接边已缓存则为零；完整event resolver共用才有轨迹等价。
当前nextUnpaidBill由完整后缀支配，不能套旧轨迹等价。proxy-to-full需加累计尾项。
own-cache账按各自资源并集计算；预算前缀只描述实际已完成账，非预计费用准入。
train simple gap、带统一偏差的valid gap、endpoint J分别证明。
-/
#check AgentUCTPaper.next_edge_allocation_iff_uct
#check AgentUCTPaper.next_edge_coupled_history_eq_uct
#check AgentUCTPaper.nextUnpaidBill_le_complete
#check AgentUCTPaper.next_edge_tail_regret_transfer
#check AgentUCTPaper.own_cache_cost_difference
#check AgentUCTPaper.own_cache_policy_regret_bound
#check AgentUCTPaper.own_cache_budget_coverage
#check AgentUCTPaper.best_training_simple_gap
#check AgentUCTPaper.validation_shortlist_gap
#check AgentUCTPaper.validation_top_one_counterexample
#check AgentUCTPaper.endpointJ_gap_identity
#check AgentUCTPaper.equal_quality_positive_endpoint_gap
#check AgentUCTPaper.next_edge_linear_regret

/-! ## G. 图的信息与压缩
交换题目/前缀求和得全panel商，完整发布维持矩形cache。
在线改价给未缓存资源加价格差；query-selective只合并相同demand-profile。
分离profile时给同聚合、费用/排序不同的见证，不宣称任意压缩均不可能。
-/
#check AgentUCTPaper.full_panel_residual_quotient
#check AgentUCTPaper.full_panel_history_rectangular
#check AgentUCTPaper.full_panel_live_completion_quotient
#check AgentUCTPaper.full_panel_live_price_update
#check AgentUCTPaper.demand_group_cost_quotient
#check AgentUCTPaper.demand_group_publication
#check AgentUCTPaper.demand_separating_merge_loses_information
#check AgentUCTPaper.GraphWitness.no_count_only_optimal_policy
#check AgentUCTPaper.ReachablePairs.active_pair_ranking_reverses

/-! ## A. 已证明结果与扩展方向
固定有限树主定理、账守恒、同状态成本条件证书与全panel费用商已证明。
以下动态结果保留其显式条件；扩展方向另建模型或证据，单独验收。
有限实际demand列表归纳给并集冷账；proposal/repair重复开销逐项保留。
生成前/后条件费用用执行law质量1展开，无独立性要求。
有效质量上界/费用下界给单步rq+gamma*rc，再对实际历史求和。
每步新资源冷账可以线性增长；增长编辑树的整树对数质量率尚未证明。
扩展方向：随机reward/失败发布/eviction、预测误差认证、test泛化、Python精化。
冻结空cache静态估价不满足覆盖后零罚项，需另分析其目标与条件。
-/
#check AgentUCTPaper.dynamic_spend_union
#check AgentUCTPaper.dynamic_spend_with_overhead
#check AgentUCTPaper.generated_completion_two_stage
#check AgentUCTPaper.dynamic_optimistic_net_loss
#check AgentUCTPaper.dynamic_optimistic_cumulative
#check AgentUCTPaper.fresh_dynamic_resource_cost
#check AgentUCTPaper.recurring_omitted_suffix
