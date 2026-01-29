import os
import re
import argparse

LINE_RE = re.compile(
    r"Vampire:\s+(\d+)\s+Minimized:\s+(N/A|\d+)"
)

def summarize(vamps, mins):
    if not vamps:
        return 0, 0.0, 0.0
    return (
        len(vamps),
        sum(vamps) / len(vamps),
        sum(mins) / len(mins),
    )

def main(log_dir):
    overall_all_v = []
    overall_all_m = []
    overall_15_v = []
    overall_15_m = []

    for filename in sorted(os.listdir(log_dir)):
        if not filename.endswith(".log"):
            continue

        file_all_v = []
        file_all_m = []
        file_15_v = []
        file_15_m = []

        with open(os.path.join(log_dir, filename), "r") as f:
            for line in f:
                match = LINE_RE.search(line)
                if not match:
                    continue

                vampire = int(match.group(1))
                minimized_raw = match.group(2)
                minimized = vampire if minimized_raw == "N/A" else int(minimized_raw)

                # per-file
                file_all_v.append(vampire)
                file_all_m.append(minimized)

                if vampire >= 15:
                    file_15_v.append(vampire)
                    file_15_m.append(minimized)

                # overall
                overall_all_v.append(vampire)
                overall_all_m.append(minimized)

                if vampire >= 15:
                    overall_15_v.append(vampire)
                    overall_15_m.append(minimized)

        # ---- per-file output ----
        c, av, am = summarize(file_all_v, file_all_m)
        c15, av15, am15 = summarize(file_15_v, file_15_m)

        print(f"\n=== {filename} ===")
        print("ALL:")
        print(f"  Count: {c}")
        print(f"  Avg Vampire:   {av:.2f}")
        print(f"  Avg Minimized: {am:.2f}")

        print("VAMPIRE >= 15:")
        print(f"  Count: {c15}")
        print(f"  Avg Vampire:   {av15:.2f}")
        print(f"  Avg Minimized: {am15:.2f}")

    # ---- overall output ----
    c, av, am = summarize(overall_all_v, overall_all_m)
    c15, av15, am15 = summarize(overall_15_v, overall_15_m)

    print("\n=== OVERALL SUMMARY (ALL FILES) ===")
    print("ALL:")
    print(f"  Count: {c}")
    print(f"  Avg Vampire:   {av:.2f}")
    print(f"  Avg Minimized: {am:.2f}")

    print("VAMPIRE >= 15:")
    print(f"  Count: {c15}")
    print(f"  Avg Vampire:   {av15:.2f}")
    print(f"  Avg Minimized: {am15:.2f}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Summarize Vampire/Minimized logs")
    parser.add_argument(
        "log_dir",
        help="Path to the directory containing .log files"
    )
    args = parser.parse_args()
    main(args.log_dir)
