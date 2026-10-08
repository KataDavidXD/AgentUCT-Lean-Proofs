"""Verify the real local stdio MCP and Lean file diagnostics, without model calls."""

import asyncio
from datetime import datetime
import json
import os
from pathlib import Path
import sys

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "theory" / "lean"


async def main():
    output = ROOT / "evidence" / datetime.now().strftime("verification-%Y%m%d") / "mcp-verification.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    report = {"status": "running", "transport": "stdio", "checks": [], "model_calls": 0}
    server = StdioServerParameters(command=sys.executable,
                                  args=["-m", "lean_lsp_mcp", "--lean-project-path", str(PROJECT)],
                                  env={**os.environ, "LEAN_LSP_MCP_LOG_LEVEL": "WARNING"})

    def save():
        output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    save()
    try:
        async with stdio_client(server) as (read, write), ClientSession(read, write) as session:
            init = await session.initialize()
            report["server"] = init.model_dump(by_alias=True, mode="json")
            tools = await session.list_tools()
            names = {tool.name for tool in tools.tools}
            required = {"lean_diagnostic_messages", "lean_goal", "lean_verify"}
            if not required <= names:
                raise RuntimeError("Required Lean MCP tools missing")
            report["available_tools"] = sorted(names)
            source = (PROJECT / "AgentUCT.lean").read_text(encoding="utf-8").splitlines()
            goal_line = next(i for i, line in enumerate(source, 1) if line.strip() == "ring")
            requests = [
                ("diagnostics", "lean_diagnostic_messages", {"file_path": "AgentUCTPaper.lean"}),
                ("goal", "lean_goal", {"file_path": "AgentUCT.lean", "line": goal_line}),
                ("axioms", "lean_verify", {"file_path": "AgentUCT.lean",
                                           "theorem_name": "AgentUCT.index_is_shifted_ucb",
                                           "scan_source": True}),
            ]
            for label, tool, args in requests:
                result = await session.call_tool(tool, args)
                payload = result.model_dump(by_alias=True, mode="json")
                report["checks"].append({"label": label, "tool": tool, "arguments": args, "result": payload})
                save()
                print(label, flush=True)
                if payload.get("isError", payload.get("is_error", False)):
                    raise RuntimeError(f"MCP tool failed: {tool}")
                structured = payload.get("structuredContent")
                if not structured:
                    for content in payload.get("content", []):
                        if content.get("type") == "text":
                            try:
                                structured = json.loads(content["text"])
                                break
                            except (ValueError, TypeError):
                                pass
                if not isinstance(structured, dict):
                    raise RuntimeError(f"Missing structured Lean response: {tool}")
                if isinstance(structured.get("result"), dict):
                    structured = structured["result"]
                if label == "diagnostics":
                    if (not structured.get("success", True) or structured.get("partial")
                            or structured.get("timed_out")
                            or any(item.get("severity") == "error" for item in structured.get("items", []))):
                        raise RuntimeError("Lean diagnostics incomplete or include errors")
                elif label == "goal":
                    line_state = bool(structured.get("goals_before")) and structured.get("goals_after") == []
                    if structured.get("status") not in {"goals", "complete"} and not line_state:
                        raise RuntimeError("No completed Lean goal-state response")
                elif label == "axioms":
                    if set(structured.get("axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}:
                        raise RuntimeError("MCP reported nonstandard theorem axioms")
            report["status"] = "passed"
            save()
            print(json.dumps({"status": "passed", "checks": len(report["checks"]), "model_calls": 0}))
    except Exception as exc:
        report["status"] = "failed"
        report["failure"] = str(exc)
        save()
        raise


if __name__ == "__main__":
    asyncio.run(main())
