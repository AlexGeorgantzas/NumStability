#!/usr/bin/env bash
set -u

audit_root=<library-repo>/tmp/library_audit/higham_v01-045daf2
worktree="$audit_root/_worktree"
src_dir="$audit_root/probes/src"
build_dir="$audit_root/probes/build"
log_dir="$audit_root/probes/logs"
status_tsv="$audit_root/probes/run_status.tsv"
commands_tsv="$audit_root/probes/run_commands.tsv"

mkdir -p "$build_dir" "$log_dir"
printf 'stem\tphase\tstarted_utc\tfinished_utc\texit_status\tfresh_output\toutput_olean\toutput_ilean\tstdout_stderr_log\ttime_log\n' > "$status_tsv"
printf 'stem\tphase\tcommand\n' > "$commands_tsv"

# P01 was executed interactively first against an empty build directory.
printf '%s\t%s\t%s\n' \
  P01_FloatingPointModel_check check \
  '/usr/bin/time -p lake env lean -R ../probes/src -o ../probes/build/P01_FloatingPointModel_check.olean -i ../probes/build/P01_FloatingPointModel_check.ilean ../probes/src/P01_FloatingPointModel_check.lean' \
  >> "$commands_tsv"
printf '%s\t%s\t%s\n' \
  P01_FloatingPointModel_client client \
  '/usr/bin/time -p lake env lean -R ../probes/src -o ../probes/build/P01_FloatingPointModel_client.olean -i ../probes/build/P01_FloatingPointModel_client.ilean ../probes/src/P01_FloatingPointModel_client.lean' \
  >> "$commands_tsv"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  P01_FloatingPointModel_check check not_recorded not_recorded 0 true \
  "$build_dir/P01_FloatingPointModel_check.olean" \
  "$build_dir/P01_FloatingPointModel_check.ilean" \
  "$log_dir/P01_FloatingPointModel_check.log" embedded_in_stdout_log \
  >> "$status_tsv"
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
  P01_FloatingPointModel_client client not_recorded not_recorded 0 true \
  "$build_dir/P01_FloatingPointModel_client.olean" \
  "$build_dir/P01_FloatingPointModel_client.ilean" \
  "$log_dir/P01_FloatingPointModel_client.log" embedded_in_stdout_log \
  >> "$status_tsv"

cd "$worktree" || exit 1
for src in "$src_dir"/*.lean; do
  stem=$(basename "$src" .lean)
  case "$stem" in
    P01_FloatingPointModel_check|P01_FloatingPointModel_client) continue ;;
  esac
  case "$stem" in
    *_check) phase=check ;;
    *_client) phase=client ;;
    *) phase=unknown ;;
  esac
  olean="$build_dir/$stem.olean"
  ilean="$build_dir/$stem.ilean"
  log="$log_dir/$stem.log"
  time_log="$log_dir/$stem.time"
  if [[ -e "$olean" || -e "$ilean" ]]; then
    fresh=false
  else
    fresh=true
  fi
  started=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  command_text="/usr/bin/time -p -o $time_log lake env lean -R $src_dir -o $olean -i $ilean $src"
  printf '%s\t%s\t%s\n' "$stem" "$phase" "$command_text" >> "$commands_tsv"
  /usr/bin/time -p -o "$time_log" \
    lake env lean -R "$src_dir" -o "$olean" -i "$ilean" "$src" \
    > "$log" 2>&1
  status=$?
  finished=$(date -u '+%Y-%m-%dT%H:%M:%SZ')
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "$stem" "$phase" "$started" "$finished" "$status" "$fresh" \
    "$olean" "$ilean" "$log" "$time_log" >> "$status_tsv"
  printf '%s %s exit=%s fresh_output=%s\n' "$stem" "$phase" "$status" "$fresh"
done
