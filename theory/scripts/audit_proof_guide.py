"""Lean comment/string masking shared by proof inventory and reading edition."""

def lean_code(text: str) -> str:
    """Mask nested comments and strings, retaining source line positions."""
    result: list[str] = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            result.extend(" " * (end - i))
            i = end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                ch = text[i]
                result.append("\n" if ch == "\n" else " ")
                i += 1
                if ch == "\\" and i < len(text):
                    result.append(" ")
                    i += 1
                elif ch == '"':
                    break
        else:
            result.append(text[i])
            i += 1
    return "".join(result)
