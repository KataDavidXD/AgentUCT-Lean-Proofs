# AgentUCT：证明背景与结果

AgentUCT 搜索有合法前缀结构的工作流。完整执行可以复用同题目的已保存 checkpoint，因此一次候选评估的新增工作随当前缓存变化。selection 使用完整反馈冷费用的预测：

$$I_h(p,a)=Q_h(pa)+c\sqrt{\frac{\log(N_h(p)+1)}{N_h(pa)}}-\gamma\widehat C_h(p,a),\qquad\gamma=\beta/C_{\rm ref}.$$

未访问 child 优先。完整评估返回 raw reward，沿展开节点及祖先回传。rollout 执行产生的前缀可以进入执行缓存；未展开前缀不会因此增加 tree visits。费用项改变 allocation，质量回传保留原定义。

## 对象与主结论

固定有限非空终局集合 $X$、前缀反链、训练奖励 $f(x)\in[0,1]$、初始缓存、价格包络、$c>0$ 与 $\gamma\ge0$。每次评估成功完成并持久发布其全 panel 需求；完成预测 law 支持合法终局、非负且总质量为一，live price 被固定有限 cap 支配。

先对固定实例选定 $\delta>0$，使它不大于任一正 edge gap；再对所有符合执行和 allocation 规则的有限历史同时给出：

$$R_Q(T)=\sum_{t=1}^T(V^*-f(x_t))\le A_D\log(T+1)+B_D.$$

$A_D,B_D$ 是实例常数，可能很大。它们不按已见历史或 $T$ 回选。主证明对实际递归树统计成立，保留非根 birth offset；没有把自适应 descendant returns 当作独立平稳 bandit 样本。

## 已证明结果

| 结果 | 数学内容 | Lean 声明入口 |
| --- | --- | --- |
| 执行与回传 | 真实计数、均值、birth deficit 与父子亏损分解 | `replayBackup_mean`, `operational_subtree_deficit_decomposition` |
| 冷费用守恒 | $C(A\mid K)+C(B\mid K\cup A)=C(A\cup B\mid K)$；同一历史的总冷账等于新发布资源并集权重 | `coldWork_sequential_union`, `replayMetered_cold_conservation` |
| 探索与覆盖 | 有限局部探索窗口推出整树覆盖；持久覆盖后完成冷罚项为零 | `finite_explicit_window_explores`, `actual_terminal_coverage`, `coldForecastPenalty_after_coverage` |
| 累计训练质量 | 子树深度归纳推出上述 $O(\log T)$ 界 | `cold_forecast_uniform_root_log_bound`, `online_mean_shared_root_log_bound` |
| 最佳已观察训练 workflow | simple gap $\le R_Q(T)/T$；全覆盖后达到固定训练表最大值 | `best_training_simple_gap` |
| 同状态费用交换 | 普通 index 最大者与定价 index 最大者的指数牺牲和预测节省有确定不等式 | `priced_choice_tradeoff` |
| 条件真实节省与净收益 | 控制价格和质量误差后得到相应真实优势下界 | `physical_saving_certificate`, `actual_net_gain_certificate` |
| 完整费用预测 | 指定真实 law 下，条件均值是平方误差的唯一最优预测值；价格误差与需求概率误差分别进入界 | `full_cost_mean_unique_mse_minimizer`, `full_reference_cost_error` |
| own-cache 轨迹与预算 | 各策略分别计实际资源账；同 $T$ 累计净 regret、事后可支付完整前缀和 endpoint 恒等式各有独立结论 | `own_cache_policy_regret_bound`, `own_cache_budget_coverage`, `endpointJ_gap_identity` |
| train 到 validation | 统一 train-valid 偏差 $\varepsilon$ 下，shortlist valid gap $\le R_Q(T)/T+2\varepsilon$ | `validation_shortlist_gap` |
| 全 panel 压缩 | 全 panel 剩余资源账可精确聚合到 prefix；异质需求下不可随意合并可被 panel 分离的 qid | `full_panel_residual_quotient`, `demand_separating_merge_loses_information` |
| 动态生成工作流 | 有限实际轨迹账守恒与带认证误差宽度的单步/累计净界 | `dynamic_spend_union`, `dynamic_optimistic_cumulative` |

预算截点可以直接代入逐历史质量界。若最后可支付完整前缀有 $T_B\ge1$ 次评估，则 training-best gap 不超过 $[A_D\log(T_B+1)+B_D]/T_B$。需要实际完成数 $T_B$；预测费用不能作为调用前准入条件。

## E1-E4 与 Q1-Q9 证明路线

E1 从 replay 递推得到真实计数/return sum/均值；E2 将均值写成 $V-D/N$；E3 保留一次 birth 项分解父节点亏损；E4 证明执行账和 checkpoint 后缀等价。

Q1 建立统一罚项包络；Q2 证明有限窗口探索；Q3 推出终局覆盖；Q4 由持久发布推出冷罚项归零；Q5 控制最优 child 的均值偏差；Q6 限制正 gap child 的访问数；Q7 对子树剩余深度和所有历史前缀归纳；Q8 在根读出质量 regret；Q9 接入在线均价、合法经验完成 law 和共享缓存。

完整假设、窗口常数、归纳系数、声明对应和反例见 [原项目理论章节快照](materials/background/AAMAS27-Theory-20261008.md) 与中英文 Lean 导读。

## 结论范围与扩展方向

固定表理论尚未给出任意预算下的全局策略最优、实用的小预算发现界、最优率/常数、held-out test 最优或 endpoint J 最优。train 与 test 的目标分别记录。当前 16 样本历史 law 的预测准确度没有认证误差半径；条件均值的 MSE 定理不直接认证实际估价器。

下一步数学工作包括随机奖励、失败发布和 eviction 模型；预测误差/费用置信半径；增长树、新资源及重复开销；validation 到 test 泛化；Python 实现到 Lean 状态转移的程序精化。动态 AFlow/GSM8K 工作流的有限轨迹账恒等式与固定有限反链树的质量率分别使用各自假设。

本仓库存放现有理论结果与历史补充材料。实验模型运行和最终 held-out 质量记录继续由私密 [AAMAS27](https://github.com/KataDavidXD/AAMAS27) 维护。
