> 2026-10-08 原项目第 6 节的理论快照；本地证明链接已适配独立仓库，其余来源链接指向 AAMAS27。历史中文 PDF 阅读入口属于原项目，当前归档按用户要求仅收录英文 PDF。

## 6. 理论与 Lean 证明

**目前已证明：在固定有限终局树、固定训练奖励、成功持久发布和有界冷费用估计下，AgentUCT 保留累计训练质量的 O(log T) 界；同状态定价给出可量化的指数—预测费用交换。** 有限预算 test F1 的优势、估费误差认证、动态编辑树的质量率、Python 对 Lean 的程序精化仍各有待解决的问题。

阅读入口：[中文 Lean 导读](../../theory/lean/AgentUCTProofGuide.lean)、[英文 Lean 导读](../../theory/lean/AgentUCTProofGuideEN.lean) → 下述假设与逐步证明 → [英文完整证明单文件](../../theory/lean/AgentUCTCompleteProofsEN.lean)。英文导读按E1–E4、Q1–Q9列出每步前提、推导、结论及五项扩展方向；96个 `#check` 显示真实完整类型。完整证明单文件按依赖顺序包含45个数学模块的全部定义、定理和证明体，并把中文步骤注释译为英文；每个SOURCE标题指向原模块。原数学源码仍由 [AgentUCTPaper.lean](../../theory/lean/AgentUCTPaper.lean) 导入，两种语言导读和英文完整证明均进入默认 `lake build`。

### 6.1 先固定对象、量词与目标

| 数学对象 | Lean 对象 | 含义 |
| --- | --- | --- |
| q、p、x | `Qid`、`List Action` | 题目、执行前缀、完整工作流 |
| X、X(p) | `terminals`、`subtreeTerminals terminals p` | 有限终局集合及 p 下的终局 |
| e_t=(v_t,x_t,f(x_t)) | `TreeEvaluation` | 一次完整评估；v_t 是实际展开节点，x_t 是 rollout 完成路径 |
| 历史 h | `List (TreeEvaluation Action)` | 只包含完整评估；`before <+: events` 表示历史前缀 |
| N、S、Q | `backedCount`、`backedReturn`、`replayBackup … .mean` | 由实际 raw reward 回传生成的统计 |
| K | `PersistentCaches.restorable` | 当前可恢复资源；`everMaterialized` 是历史已发布集合 |
| C(D\|K) | `coldWork weight cached demand` | 对 D\K 求和；预测权重与物理账本各有自己的参数 |
| V(p)、Δ(p,a) | `subtreeValue`、`edgeGap` | p 下最大固定训练奖励及 child gap |
| D_t(p) | `backedDeficit (subtreeValue … p) events p` | 经过 p 的已完成 return 相对 V(p) 的累计亏损 |
| γ | `gamma = beta / C_ref` | selection 定价系数；区别于报告 J 的 λ/C_ref 和累计净目标的 η |

主结论的量词顺序是 **先固定实例并取 δ>0，再对所有合法有限历史给出界**：

```text
固定 terminals、reward、c、gamma、预测包络和初始持久缓存
→ ∃ delta > 0
→ ∀ events，FixedTableEvents ∧ LegalTreeRun ∧ TreeAllocationRule
→ D_T(root) ≤ A_D * log(T+1) + B_D
```

δ 不按已见历史或 T 回选。有限树的正 gap 有统一正下界；所有 gap 为零时仍可取任意正 δ。T 是完整全 panel 评估数，包含零新增费用的 cache replay。

### 6.2 主定理假设逐项列清

| 假设 | Lean 入口 | 在证明中的用途 |
| --- | --- | --- |
| X 非空且有限 | `Finset`、`hTerminals` | 最大值可取到、资源并集有限、常数为有限值 |
| 终局是前缀反链 | `hAntichain` | 终局下面不存在另一个终局，终局 deficit 为零 |
| f(x)∈[0,1] 且每次 return 等于同一 f(x) | `hReward`、`FixedTableEvents` | 均值有界、gap 固定、子树 deficit 恒等式 |
| 一次至多插入一个 child，raw reward 只回传展开节点及祖先 | `LegalTreeRun`、`replayBackup` | birth 最多一次、局部流与整树一致 |
| 未访问 child 优先，其余最大化实际 index；c>0、γ≥0 | `TreeAllocationRule`、`hc`、`hGamma` | 有限窗口内初始化与反复探索 |
| 每次成功发布完整终局的全 panel 需求，持续保留 | `replayPublished`、`hInitial` | 历史已发布资源等于可恢复资源；覆盖后罚项为零 |
| 0≤live_h(r)≤base(r)，base 是固定有限包络 | `hLive`、`hUpper`；在线均值版 `hPrior`、`hValue` | 所有历史的冷费用罚项均被同一 H 支配 |
| law_h,p,a 支持合法完成、非负且总质量 1 | `hLaw`、`hMass` | 完成费用是有限加权平均，因此有界 |

最深 checkpoint 后缀等价另用 `prefixComplete`；主质量率核心用的是完整成功发布与 `restorable = everMaterialized`。额外共享 cache 可以任意增加可恢复内容，不把别的 panel 的奖励回传给本树。预测 cap 只约束估计值；物理费用继续按实际全额记录，不用 cap 或 H 拒绝模型调用。

当前固定 greedy 设置下曾观测同配置答案变化，故 `FixedTableEvents` 是理论模型的执行假设。本轮真实运行没有证明它逐条成立。固定训练表的最大值也不等于 test 最优值。

### 6.3 执行与回传：质量证明的起点

**步骤 E1：从回传递推得到真实计数和均值。** 对 `events` 归纳；每个 event 只在 p 为 v_t 前缀时给 N 加1、S 加 f(x_t)。得到 N=Σ1[p≼v_t]、S=Σ1[p≼v_t]f(x_t)、Q=S/N。rollout 未展开节点可进执行 cache，其 tree visits 不随之增加。声明：`replayBackup_visits`、`replayBackup_rewardSum`、`replayBackup_mean`、`rollout_publication_without_backup`。

**步骤 E2：把均值偏差改写为 deficit。** 定义 D=N·V−S；N>0 时消去非零分母，得到 Q=V−D/N。每个 return 都来自 p 下合法终局，因此 D≥0、Q≤V。终局反链及固定 reward 使终局每个亏损项为零。声明：`backedDeficit_identity`、`operational_mean_deficit`、`operational_mean_le_subtreeValue`、`terminal_backedDeficit_zero`。

**步骤 E3：保留 birth 项，分解父节点。** 将经过 p 的事件分为 v_t=p 和按下一动作 a 进入 pa 的事件，得到

\[
D_t(p)=d_t^{birth}(p)+\sum_a\{N_t(pa)\Delta(p,a)+D_t(pa)\}.
\]

非根内部节点插入时只发生一次 birth，0≤d_birth≤1；根 birth=0。局部动作流只包含进入 child 的事件，父计数为局部长度加 o，根 o=0，已插入非根内部节点 o=1。声明：`operational_subtree_deficit_decomposition`、`internal_birthDeficit_le_one`、`localBefore_parent_count`、`projected_index_max`。这里没有把自适应 descendant returns 当作独立平稳 bandit 样本。

**步骤 E4：同一历史的执行账守恒。** D\K 与 K 不交，发布 K←K∪D；单步新增账等于新资源权重，逐步相消得到总冷账。任意重叠需求 A、B 满足

\[
C(A\mid K)+C(B\mid K\cup A)=C(A\cup B\mid K).
\]

不同 qid 的资源键不交；在前缀完整条件下，缺失资源恰好是每题最深可恢复 checkpoint 之后的后缀。声明：`replayMetered_cold_conservation`、`coldWork_sequential_union`、`coldWork_eq_deepest_suffix`。固定权重守恒按相应数学模型使用；真实在线价不能回改历史物理账。

### 6.4 整树对数界：逐步闭合

**步骤 Q1：建立统一罚项包络。** 令 R 为所有合法终局需求的并集，H=γΣ_{r∈R}base(r)。每个合法完成的 missing 需求是 R 的子集；live≤base；law 非负且质量1。因此 0≤penalty_h(p,a)≤H。声明：`referenceColdCost_bounded`、`coldForecastPenalty_bounded`、`completion_prediction_envelope`。H 是数学预测包络，尚未说明实际搜索费用或误差半径。

**步骤 Q2：有限窗口迫使所有 child 继续被探索。** 对分支数 k、目标次数 m，源码取

\[
L(k,m)=\Big\lceil\max\{k+1,\exp(((H+2)^2m+1)/c^2),
(8k\max(1,c^2)+2)^2\}\Big\rceil.
\]

Q2.1：未访问优先在前 k 次局部选择内完成初始化。Q2.2：反设某 child 在 2L 时仍≤m 次；在 [L,2L) 内它的 bonus>H+2，故 index>2。Q2.3：被选 child 的 Q≤1、penalty≥0，故其 bonus>1，选择前次数<c²log(2L+o+1)。Q2.4：同一 child 的这些次数严格增长，整个窗口最多容纳 k[c²log(2L+o+1)+1] 次。Q2.5：由 log z≤2√z 与 L 的平方项，上式<L，和窗口内恰有 L 次选择矛盾。因此每 child 在 2L 次后都>m。声明：`initialized_after_unvisited_first` → `selected_count_under_pressure` → `small_count_window_bound` → `finite_window_explores` → `finite_explicit_window_explores` → `actual_children_explored`。

**步骤 Q3：从局部探索推出整树覆盖。** 定义 C_0=1，C_{d+1}=1+max_p 2L(k_p,C_d)。按剩余深度归纳：终局正访问即被观察；内部节点去掉至多一次 birth 后，仍有足够局部选择；Q2 使各 child 超过 C_d，归纳覆盖每个子树。根 N=T，故 T_cache=C_D 后所有终局均被观察。声明：`actual_subtree_coverage`、`actual_terminal_coverage`。

**步骤 Q4：覆盖使全部冷罚项严格为零。** 终局访问发布全 panel 的全部前缀，所以 R⊆K；每个未来合法完成的 D(x)\K=∅。先得到可恢复资源覆盖，再由空有限和得到 penalty=0。声明：`actual_restorable_coverage` → `referenceColdCost_zero` → `coldForecastPenalty_after_coverage`。共享 cache 的额外并集只使 missing 集合更小。**罚项有界只证明 Q2/Q3；Q4 才允许闭合后面的质量率。**

**步骤 Q5：把子树对数亏损变成最优 child 的均值下界。** 先固定 δ>0≤所有正 gap。若孩子归纳界为 D(n)≤A_d log(n+1)+B_d，取

\[
m_d=\Big\lceil\max\{1,(32A_d/\delta)^2,8B_d/\delta\}\Big\rceil.
\]

由 log(n+1)≤4√n 得到 n≥m_d 时 D(n)/n≤δ/4。Q2 保证过有限局部阈值后所有 child 的 N>m_d；选取 V(pa*)=V(p) 的最优 child，并用 E2 得到 Q(pa*)≥V(p)−δ/4。声明：`finite_tree_positive_edge_gap`、`biasVisitTarget_bounds`、`logarithmic_deficit_small`、`internal_has_optimal_child`。

**步骤 Q6：限制正 gap child 的访问次数。** 令

\[
\tau_d=\max_p\max\{T_{cache},2L(k_p,m_d)\}.
\]

Q6.1：局部时间≥τ_d 时，全球历史长度也≥T_cache，两个比较候选罚项都为零。Q6.2：若正 gap child a 被选，实际 index 最大性与 Q(a)≤V(pa)、Q(a*)≥V(p)−δ/4，使 a 的 bonus≥δ/2。Q6.3：平方 bonus 恒等式并乘正分母，得到选择前 N(pa)≤4c²log(N(p)+1)/δ²。Q6.4：所有早期选择≤τ_d；晚期次数使用最终父计数统一上界，再加最后一次增量，得到

\[
N_T(pa)\le\tau_d+4c^2\log(N_T(p)+1)/\delta^2+1.
\]

声明：`selected_count_from_subtree_bias` → `count_le_burnin_add_cap` → `actual_suboptimal_child_count`。额外 +1 和 non-root 的 birth offset 都保留，未把离散时间写成连续近似。

**步骤 Q7：对子树剩余深度归纳。** 终局 D=0，因此 A_0=B_0=0。将 Q6 和孩子界代入 E3；正 gap 的 Δ≤1，零 gap 的 NΔ=0，孩子计数≤父计数，分支数≤K=max_p k_p，得到

\[
A_{d+1}=K(A_d+4c^2/\delta^2),\qquad
B_{d+1}=1+K(B_d+\tau_d+1).
\]

归纳需对**所有历史前缀**同时成立，才可用于某次选择之前的孩子统计。源码 `induction depth generalizing events p` 保留这一点，`run.prefix` 与 `hTable.prefix` 传递历史前缀条件。声明：`parent_deficit_log_bound` → `actual_subtree_log_deficit`。

**步骤 Q8：在根读出累计质量 regret。** 根被每个完整 event 回传一次，N(root)=T、D(root)=Σ(V*−f(x_t))，Q7 立即给出

\[
R_Q(T)\le A_D\log(T+1)+B_D.
\]

`cold_forecast_uniform_root_log_bound` 接固定预测；`shared_cache_uniform_root_log_bound` 接共享发布；`dominated_cold_shared_root_log_bound` 接被固定完成冷费用支配的罚项；`checkpoint_conditioned_shared_root_log_bound` 接随历史变化的有界价格。这里名称中的 `uniform_root` 表示同一实例常数适用于所有合法历史，不要求 rollout 为均匀采样。常数可以嵌套指数增长，这个定理没有给出实用的小预算发现保证。

**步骤 Q9：连接当前在线均价与16样本。** `onlineMean`=(prior+Σ物理样本)/(1+样本数)。prior 与每个裁剪预测样本位于[0,cap]，有限和≤样本数·cap，正分母给出均价仍在[0,cap]。`sampledLaw` 按 `Fin n` 样本索引计概率：重复完成保留多次质量；交换有限和证明期望为样本账均值，n>0 时总质量1。声明：`onlineMean_envelope`、`sampledLaw_expectation`、`sampledLaw_mass`、`onlineMean_completion_envelope` → `online_mean_shared_root_log_bound`。16样本的准确度未被这条链证明；任意合法经验 law 已足够满足渐近包络条件。

### 6.5 同状态成本选择：证明与可用结论

固定同一树、cache、候选集与 U。b 最大化 U，a 最大化 U−γĈ，γ>0。

1. 普通最大性给 U(a)≤U(b)。
2. 定价最大性移项给 U(b)−U(a)≤γ[Ĉ(b)−Ĉ(a)]。
3. 左边≥0 且 γ>0，故 Ĉ(a)≤Ĉ(b)。
4. 合并得到 `priced_choice_tradeoff`：0≤指数牺牲≤γ·预测节省。
5. 若 |Ĉ(a)−C(a)|≤ε_a、|Ĉ(b)−C(b)|≤ε_b，用 `abs_le.mp` 拆双边误差：C(b)−C(a)≥Ĉ(b)−Ĉ(a)−ε_a−ε_b。这是 `physical_saving_certificate`。
6. 若还控制 U 与真实质量的偏差，则指数净优势减质量误差和与 γ 倍费用误差和，才得到真实净优势下界：`actual_net_gain_certificate`。

这里 U 含探索 bonus，不能直接解释成下一条工作流的真实 F1；C 在条件期望解释下须由所声明的条件 law 提供。当前保存的选择表可验前4项算术关系；未选候选缺少同状态反事实物理账，当前估价器也没有认证误差半径，所以后两项是条件证书。`priced_choice_no_universal_quality_dominance` 保留了可检查的数值见证；它不构成所有树算法的不可改进定理。

完整费用预测另有资源形式与误差分解：交换终局/资源有限和得到 `referenceColdCost_resource_form`；价格误差与需求概率误差逐项用三角不等式汇总为 `full_reference_cost_error`。条件均值的平方损失恒等式 MSE(z)=Var(C)+(z−E[C])² 给出 `full_cost_mean_unique_mse_minimizer`。这是指定 law 下的目标定义，未证明当前历史 law 等于实际未来 UCT 条件分布。费用 LCB 的乐观分配结论要求有效置信半径，当前主算法尚无该认证。

### 6.6 Next、轨迹、预算和最终选优分别回答什么

| 结果 | 推导步骤 | 结论范围 |
| --- | --- | --- |
| 旧 immediate 的 UCT 退化 | child 被回传→该完整前缀已发布→直接边冷账0→index相同 | `next_edge_allocation_iff_uct` 针对旧 `nextEdgePenalty`；共用 event resolver / rollout / tie / stopping 才有整轨迹相同 |
| 当前 NextC 的质量率 | 每题第一条正价未付费边≤同样本完整 missing 后缀→固定包络→覆盖后0→Q7/Q8 | `nextUnpaidBill_le_complete`、`dominated_cold_shared_root_log_bound`；不把旧 immediate 定理改称当前 NextC 轨迹等价 |
| Next proxy→Complete 局部净值 | 每步 full gap=proxy gap+η·(chosen tail−comparator tail)，逐项求和 | `next_edge_tail_regret_transfer` 加 ηΣtail variation；该和不受控时无法推出所对应局部目标的对数率 |
| 不同策略自身cache费用 | 各自账分别等于新发布资源并集权重；消去共有资源 | `own_cache_cost_difference`；局部便宜不推出整条策略便宜 |
| 同 T 的累计 own-cache 净regret | comparator 每个固定表 reward≤V*；实际新增冷账≤W；组合质量界 | `own_cache_policy_regret_bound` 给 R_net≤R_Q+ηW；相等总 recurring overhead可抵消，其他情况保留差项 |
| 预算内完成数 | 各策略**实际完成费用**分别有上下界；有限和与非负前缀单调性 | `own_cache_budget_coverage`；只描述事后可支付完整前缀，不能充当调用前预计费用准入，也不推出质量改善 |
| 最佳已见 train 质量 | 全部 return≤best observed；总亏损≥T·simple gap | `best_training_simple_gap` 给 train gap≤R_Q/T；没有 test 分布保证 |
| Top-k→validation | k>0 保留 train head；它的 train gap≤R_Q/T；全终局 train–valid偏差≤ε 两次转移 | `validation_shortlist_gap` 给 valid gap≤R_Q/T+2ε；未提供实际 ε 或 valid→test保证 |
| endpoint J | 展开 J=quality−λcost/C_ref，直接移项 | `endpointJ_gap_identity`；质量相同且多付费时 J 严格更低，累计regret不能替代endpoint结论 |

预算截点也能直接接主质量界：该界逐历史、逐完整前缀成立，因此事后最后可支付前缀有 T_B≥1 次评估时，最佳已观察训练工作流的 gap≤[A_D log(T_B+1)+B_D]/T_B。这里把该前缀代入质量界，再用 `best_training_simple_gap`；不需要把随机停止时间当独立事件或新增optional-stopping假设。它依赖实际完成数 T_B，没有给出关于支出 B 的最优率，也没有给出 valid-selected test 界。

反例分别保留：`validation_top_one_counterexample` 展示全观察也可能排除 valid 最优；`next_edge_linear_regret` 展示**指定平稳局部 proxy UCB 与重复尾账**的线性 full-net 损失，不套到有限持久冷账体系。固定action cost的平移UCB恒等式也不证明整个自适应树等于经典独立样本UCB1。

### 6.7 图信息、压缩与动态工作流

**全 panel 商状态。** 将 Σ_q Σ_prefix 交换为 Σ_prefix Σ_q 得到 `full_panel_residual_quotient`。每次发布 Q×P_x；由 (Q×S)∪(Q×P_x)=Q×(S∪P_x) 对历史归纳，得到 `full_panel_history_rectangular`。`full_panel_live_completion_quotient` 对任意当前价格仍成立；`full_panel_live_price_update` 把未缓存资源的价格差加到剩余聚合量，旧总数本身不决定新价。商状态充分支持估费，执行仍要真实checkpoint内容。

**query-selective 边界。** 仅当两 qid 在所有允许 panel 的成员关系相同，才可按 demand-profile 合并。对分组内求和得到 `demand_group_cost_quotient`，按完整分组发布得到 `demand_group_publication`。若有 panel 能分离它们，构造两个聚合相同、被需求缓存位置相反的状态，费用或可支付性反转；`demand_separating_merge_loses_information` 与 `GraphWitness` 证明指定聚合丢失信息。`ReachablePairs.active_pair_ranking_reverses` 给出可达状态中的排序反转见证。当前固定全 panel 实验没有不可压缩显式图的必要性结论。

**动态生成程序。** `dynamic_spend_union` 对有限实际 demand 列表归纳，用 E4 合并全部 cold 账；资源类型和未来程序可事先未知。`dynamic_spend_with_overhead` 保留 proposal/repair 重复账。`generated_completion_two_stage` 用各 child 内执行law质量1与分配律，展开生成前期望为生成后条件期望；它不要求独立性。`dynamic_optimistic_net_loss` 用有效奖励上界、费用下界和选择最大性得到单步 rq+γrc 界，`dynamic_optimistic_cumulative` 对实际历史逐步相加。当前程序生成并没有认证这些误差宽度。

`fresh_dynamic_resource_cost` / `recurring_omitted_suffix` 展示每步新资源即使旧 cache 持久，累计冷账仍可为 T。动态编辑空间、内部节点也可评估、不断出现新程序时，有限反链与固定有限资源条件需要另建模型，未得到 AFlow 的整树 O(log T) 质量定理。

### 6.8 已证明结果与扩展方向

现有证明覆盖固定有限树的质量率、执行账守恒、同状态成本条件证书和全panel费用商。下表列出已成立的结果、实验评价及各自的适用范围。扩展方向涉及新的假设或证据，单独验收。

| 主题 | 已成立的结果与适用范围 | 扩展方向 |
| --- | --- | --- |
| 定价与质量探索 | 第6.2节条件下Q1–Q9已闭合，得到按完成评估数T计的质量界 | 随机reward、失败发布和eviction模型下的替代质量证明 |
| 同状态成本与净值 | 预测费用交换关系及带ε的真实节省/净值条件证书已证明 | 为当前估价器认证误差半径，识别未选候选的同状态条件成本 |
| 同预算test F1（实验评价） | 已完成cohort按实际收费和实验结果报告；T包含免费replay | 若主张test理论保证，另建预算与泛化条件；现有界不推出普遍优胜或log预算率 |
| 静态完整费用消融 | 冻结空cache预测不随真实cache归零；当前主定理不覆盖该对照 | 分析其独立目标或补足新条件；当前保留有限预算实验比较 |
| 全panel费用压缩 | 精确费用商已证明；恢复执行仍需checkpoint内容 | 将已有需求profile与分离结果接入query-selective实验 |
| 训练与validation推荐 | train simple gap及带统一偏差ε的valid界已证明 | 在分布与选择假设下建立最终test泛化界 |
| 动态程序与AFlow | 有限轨迹账守恒与条件单步净界已证明 | 为增长树、新资源和重复开销另证累计质量率 |
| Lean与Python实现 | 数学模型及抽象操作事件已形式化并通过编译 | 建立Python到Lean的状态对应与逐步程序精化证明 |

当前理论验收以已声明定理及其显式前提为准；表中的扩展按 [TODO.md](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/TODO.md) 单独安排，优先连接随机奖励和预测误差认证。旧 `Probability`、`Expected`、`Regret`、`GreedyExpected` 的概率/局部bandit结果保留各自的固定gap、confidence/sampling前提，不用于替代Q1–Q9整树证明。

### 6.9 Lean 阅读习惯与验证

| 阅读步骤 | 具体证明源 |
| --- | --- |
| E1–E3 回传、均值与父分解 | [TreeBackup](../../theory/lean/AgentUCTPaper/TreeBackup.lean)、[TreeReturns](../../theory/lean/AgentUCTPaper/TreeReturns.lean)、[TreeDecomposition](../../theory/lean/AgentUCTPaper/TreeDecomposition.lean) |
| E4 实际冷账与恢复 | [TreeExecution](../../theory/lean/AgentUCTPaper/TreeExecution.lean)、[TreeCheckpoint](../../theory/lean/AgentUCTPaper/TreeCheckpoint.lean) |
| Q1–Q4 探索、覆盖、零罚项 | [TreeAllocation](../../theory/lean/AgentUCTPaper/TreeAllocation.lean)、[TreeWindow](../../theory/lean/AgentUCTPaper/TreeWindow.lean)、[TreeCoverage](../../theory/lean/AgentUCTPaper/TreeCoverage.lean)、[TreeForecast](../../theory/lean/AgentUCTPaper/TreeForecast.lean) |
| Q5–Q8 子树偏差、次数、整树归纳 | [TreeRateAlgebra](../../theory/lean/AgentUCTPaper/TreeRateAlgebra.lean)、[TreeRateStep](../../theory/lean/AgentUCTPaper/TreeRateStep.lean)、[TreeRate](../../theory/lean/AgentUCTPaper/TreeRate.lean) |
| Q9 在线实现与共享缓存 | [OnlineMean](../../theory/lean/AgentUCTPaper/OnlineMean.lean)、[TreeSharedCache](../../theory/lean/AgentUCTPaper/TreeSharedCache.lean)、[DynamicCompletion](../../theory/lean/AgentUCTPaper/DynamicCompletion.lean) |
| 同状态定价与误差 | [TreeDecisionValue](../../theory/lean/AgentUCTPaper/TreeDecisionValue.lean)、[TreeCostEstimation](../../theory/lean/AgentUCTPaper/TreeCostEstimation.lean)、[TreeEstimatorChoice](../../theory/lean/AgentUCTPaper/TreeEstimatorChoice.lean) |
| Next、预算、净目标、推荐 | [TreeNextUnpaid](../../theory/lean/AgentUCTPaper/TreeNextUnpaid.lean)、[TreeReduced](../../theory/lean/AgentUCTPaper/TreeReduced.lean)、[TreeFiniteBudget](../../theory/lean/AgentUCTPaper/TreeFiniteBudget.lean)、[TreeObjectives](../../theory/lean/AgentUCTPaper/TreeObjectives.lean)、[TreeRecommendation](../../theory/lean/AgentUCTPaper/TreeRecommendation.lean) |
| 全panel、需求profile与在线价商 | [TreeGraphInformation](../../theory/lean/AgentUCTPaper/TreeGraphInformation.lean)、[TreeDemandQuotient](../../theory/lean/AgentUCTPaper/TreeDemandQuotient.lean)、[FullPanelLivePrices](../../theory/lean/AgentUCTPaper/FullPanelLivePrices.lean) |

Lean声明先读冒号前的显式假设，再读冒号后的结论；`by` 后才是证明。`intro` 固定任意对象，`obtain` 拆存在/合取，`have` 给中间命题命名，`calc` 链接等式/不等式，`rw` 应用已证恒等式，`apply` 将目标拆为充分条件。`linarith` / `nlinarith` 只闭合已列前提的代数关系；`omega` 处理自然数计数；它们不验证物理模型或统计假设。

本轮参考社区 [lean4技能](https://github.com/cameronfreer/lean4-skills/blob/main/plugins/lean4/skills/lean4/SKILL.md) 的保留声明、显式中间目标和公理检查习惯，使用项目现有编译环境；无需安装其插件。关键证明正文的步骤编号与Q1–Q9对应，导读由Lean检查全部引用名。

固定版本为 Lean 4.24.0 / mathlib v4.24.0。历史3299-target构建记录保留在 [algorithm build](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/theory/evidence/algorithm/lean-build.log)；本轮构建、全部源码定理依赖和无占位扫描单独保存于 `theory/evidence/proof-guide-20261004/`，实际结果追加 [EXPERIMENT_RECORDS.md](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/EXPERIMENT_RECORDS.md)。公理检查允许标准 `propext`、`Classical.choice`、`Quot.sound`，检查 `sorryAx` 与项目自定义公理另列。

已安装固定版本环境时，在 `theory/lean` 执行 `lake build`；本机现成WSL环境为 `~/.cache/agentuct-proof-20261001/project`，可由 `theory/scripts/check_proof_guide_wsl.sh` 同步源码并构建，不覆盖旧证据。仅运行CPU证明检查，不新增实验fingerprint/SHA/源字节门槛，不调用模型、不改变GPU锁/holder、物理账或事后snapshot规则。

**Windows VS Code 验证（2026-10-04）：** 原目录 `theory/lean` 已用 Windows 原生 Lean 4.24.0 构建通过，覆盖49个默认入口/依赖源码及另外7个Audit入口，共56个 `.lean` 源文件；中英文导读各96个声明引用均通过。证据在 [Windows编译验收](../../evidence/historical/vscode-native-20261004/verification.json)。WSL副本的构建产物不会更新 Windows 原目录；编辑器提示 `Imports are out of date` 时应在它实际使用的目录重建。项目 `.vscode/settings.json` 已开启 `lean4.automaticallyBuildDependencies`，用VS Code打开 `theory/lean` 文件夹后生效。默认构建任务 `Lean: Check all project sources (Windows)` 调用 `python theory/scripts/check_lean_windows.py`，在原目录补齐Mathlib标准缓存、编译全部源码并检查审计入口。首次原生构建所需3236个Mathlib缓存已下载并解包；没有修改数学定理。

InfoView 的绿色96条信息是导读 `#check` 输出的声明类型。光标在 `import` 或没有附带类型信息的位置时，`No info found` 是正常提示；选中下方声明可读参数、前提与结论。若编辑器仍保留重建前的导入错误，执行 `Lean 4: Server: Restart File` 刷新当前文件。

英文单文件由 `python theory/scripts/build_english_proof_bundle.py` 生成；修改数学内容时编辑原模块，再重新生成。它只依赖Mathlib，可独立检查全部项目证明；下游文件选择导入 `AgentUCTCompleteProofsEN` 或 `AgentUCTPaper`，避免同时导入两个定义同名声明的入口。英文导读导入完整单文件，因此其公理检查直接检查该版本的证明。英文版本的源码位置映射、编译和公理日志保存于 `theory/evidence/proof-guide-en-20261004/`。复现：先运行 `python theory/scripts/audit_proof_guide.py prepare --guide AgentUCTProofGuideEN --evidence proof-guide-en-20261004`，再调用WSL的 `check_proof_guide_wsl.sh proof-guide-en-20261004`，待编译和公理检查全部结束后运行相同参数的 `audit_proof_guide.py finish`。

[英文合订阅读稿](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/Agentic_Optimization/output/pdf/english-proofs-20261004/Technical%20Supplement.pdf) 是本轮保留的50页快照，包含15页主稿与参考文献、35页补充材料；数学证明与形式验证章节位于原PDF第44–50页，共7页。文件原名来自论文工程入口；它包含主文，不能直接作为独立补充材料提交。完整机器检查证明仍以 `.lean` 源码为准。

用户限定本轮只处理补充材料与证明。独立阅读文件为：

- [中文理论与逐步证明导读（7页）](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/Agentic_Optimization/output/pdf/proof-reading-20261004/AgentUCT_Theory_and_Proof_Guide_ZH.pdf)：对象、量词与假设，E1–E4操作语义，Q1–Q9主证明，条件净值/预算/推荐结论，已证明结果与扩展方向及一个完整Lean证明示例。385个定理的完整机器证明体仍在Lean源码中。
- [英文证明与形式验证章节（8页）](../pdf/AgentUCT_Proof_Sections_EN.pdf)：由 [Proofs_Standalone_EN.tex](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/Agentic_Optimization/Proofs_Standalone_EN.tex) 独立编译，包含“Proven Results and Extension Directions”。章节、公式和表格从1独立编号；主文引用标为 `M.`，完整补充材料引用标为 `S.`。完整机器证明体仍在Lean源码中。
- [独立英文补充材料（40页，含上述证明及所引文献）](../pdf/AgentUCT_Supplement_Only_EN.pdf)：由 [Supplement_Standalone_EN.tex](https://github.com/KataDavidXD/AAMAS27/blob/codex/rag-small-model-selection/Agentic_Optimization/Supplement_Standalone_EN.tex) 独立编译，复用现有补充源文件，不含主文。公式、图、表从1编号，主文引用标为 `M.`。采用10pt单栏阅读版，修复长名称/路径越界、标题留白及不必要的强制分页。历史50页合订稿和截页版另保留。

构建入口为 `theory/scripts/build_proof_reading_pdfs.py`，用配置了ReportLab/pypdf的Python运行：中文由已有README与证明源生成；英文调用 `build_standalone_english_readers.py`，从TeX独立编译，不再截页导出。外部主文编号读取现有 `output/pdf/AnonymousSubmission2027.aux`，主文更新编号后应重建阅读版。当前英文两册均已全页渲染目视，字体嵌入、文字边界和引用解析通过；证据在 [独立编译](../../evidence/historical/standalone-readers-20261004/build.json) 与 [页面验收](../../evidence/historical/standalone-readers-20261004/layout-review.json)。本轮只改阅读版排版，数学证明与实验结果未改；主文源码和主文PDF未编辑。

[AAMAS 2027官方说明](https://warwick.ac.uk/fac/sci/dcs/aamas2027/guidelines-and-policies/instructions/)未列补充材料页数上限，要求单个ZIP不超过25MB，并说明审稿人可不读补充材料、重要论证应在主文提供。独立补充材料作为完整复核材料保留；阅读入口建议使用8页证明册，正式补充包须另核对匿名性和披露。

