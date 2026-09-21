# Concurrent Linearizability Specification in Verus

这个仓库包含一个用 Verus 编写的并发历史线性化规格：

- [`linearizability_concurrent_spec.rs`](linearizability_concurrent_spec.rs)：定义顺序数据库语义、并发调用历史、线性化见证以及最终的 `linearizable` 判定。

## 模型内容

规格中的抽象数据库是一个从键到整数值的 `Map`，支持四类操作：

- `Get(key)`：读取一个键；
- `Put(key, value)`：插入或覆盖一个键值；
- `Scan(lo, hi)`：返回闭区间 `[lo, hi]` 内按键严格排序的全部记录；
- `Sort`：返回整个数据库按键严格排序后的全部记录。

`database_step` 给出这些操作的顺序语义。并发历史中的每次调用由 `CallRecord` 表示，记录线程、操作、调用时间、返回时间和结果。不同调用的时间区间可以重叠。

`LinearizationWitness` 是线性化的见证，包含：

- 所选操作的顺序 `order`；
- 每个操作在线性化历史中的结果 `outcomes`；
- 每一步前后的抽象数据库状态 `states`。

最终的 `linearizable(initial, history)` 要求存在一个见证，同时满足：

1. 每个已完成调用都在线性化顺序中恰好出现一次；
2. 尚未完成的调用可以省略，也可以按合法结果补全后加入；
3. 如果调用 A 在调用 B 开始前已经返回，那么 A 必须排在 B 前面；
4. 见证中的每一步都符合 `database_step` 定义的顺序数据库语义。

## 验证

安装 Verus 后运行：

```powershell
& "D:\path\to\verus.exe" ".\linearizability_concurrent_spec.rs"
```

当前验证结果：

```text
verification results:: 1 verified, 0 errors
```

文件末尾的空 `main` 只是为了让它能够作为独立文件交给 Verus CLI；这个仓库的主要内容是规格，而不是运行时演示程序。

## 当前边界

这个文件定义并检查“什么样的并发历史是可线性化的”，但尚未把某个真实的并发数据库实现连接到该规格。因此，它本身不代表任何具体 Rust、C++ 或数据库实现已经被证明可线性化，也不包含死锁、饥饿或公平性等活性证明。
