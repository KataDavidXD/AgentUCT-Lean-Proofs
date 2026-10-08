"""Run explicit Lean LSP requests in the existing isolated proof environment."""

import argparse
import asyncio
import json
from pathlib import Path

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--requests", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    requests = json.loads(args.requests.read_text())
    server = StdioServerParameters(command="lean-lsp-mcp", args=["--lean-project-path", str(args.project)])
    report = {"requests": requests, "results": []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    async with stdio_client(server) as (read, write), ClientSession(read, write) as session:
        await session.initialize()
        for request in requests:
            if request["tool"] == "list_tools":
                result = await session.list_tools()
                payload = [t.model_dump() for t in result.tools if t.name in request["names"]]
            else:
                result = await session.call_tool(request["tool"], request["args"])
                payload = result.model_dump(by_alias=True)
            report["results"].append(payload)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
            print(json.dumps({"tool": request["tool"], "result": payload}), flush=True)


if __name__ == "__main__":
    asyncio.run(main())
