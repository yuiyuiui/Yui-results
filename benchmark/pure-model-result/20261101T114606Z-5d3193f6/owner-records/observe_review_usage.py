"""Passive native reviewer cumulative usage observation, with disjoint role accounting."""
import datetime,json,pathlib
root=pathlib.Path(__file__).resolve().parent.parent
owner=root/'owner-records'
allowed={'01a197b1-0aeb-7fd1-b6d4-f1f63aab268a'}
sessions={}
for home in sorted(root.glob('review-*-home')):
    for path in sorted((home/'sessions').rglob('*.jsonl')):
        current=None
        for line in path.open():
            try:event=json.loads(line)
            except json.JSONDecodeError:continue
            payload=event.get('payload',{})
            if event.get('type')=='session_meta':current=payload.get('id')
            if event.get('type')!='event_msg' or payload.get('type')!='token_count':continue
            usage=(payload.get('info') or {}).get('total_token_usage')
            if not usage:continue
            assert current in allowed, 'Unexpected evaluator session; audit before aggregation'
            prior=sessions.get(current)
            if prior and usage.get('total_tokens',0)<prior['usage'].get('total_tokens',0):
                raise RuntimeError('Reviewer cumulative usage decreased; baseline audit required')
            sessions[current]={'path':str(path),'timestamp':event.get('timestamp'),'ordinal':event.get('ordinal'),'usage':usage}
accounting=json.loads((owner/'accounting.json').read_text())
fields=('input_tokens','cached_input_tokens','output_tokens','reasoning_output_tokens','total_tokens')
observed={k:sum(s['usage'].get(k,0) for s in sessions.values()) if sessions else None for k in fields}
now=datetime.datetime.now(datetime.timezone.utc)
accounting['observed_at_utc']=now.isoformat()
accounting['supplement']['review_observed_usage']=observed
accounting['supplement']['review_raw_snapshot_receipt']=sessions
accounting['supplement']['review_usage']='Latest per-session native cumulative snapshots with fresh-session zero baseline; never sum cumulative snapshots. Cached/reasoning are subsets; in-flight generation may be unreported. Not a substitute for unexposed provider/account costs.'
start=json.loads((owner/'measurement-start.json').read_text())
elapsed=(now-datetime.datetime.fromisoformat(start['operator_interval_start_utc'])).total_seconds()
accounting['supplement']['end_to_end_observed_seconds']=elapsed
accounting['historical_plus_supplement_wall_seconds_so_far']=24181.945501083974+elapsed
author=accounting['supplement'].get('author_observed_usage',{})
if all(observed.get(k) is not None and author.get(k) is not None for k in ('input_tokens','output_tokens')):
    inp=190088829+author['input_tokens']+observed['input_tokens']
    out=861602+author['output_tokens']+observed['output_tokens']
    accounting['combined_including_review_observed_total']={'input_tokens':inp,'output_tokens':out,'input_plus_output_tokens':inp+out,'scope':'Historical original plus measured author and independent evaluator native snapshots; owner/provider/account missing usage remains PARTIAL, not zero. No overlap with separate owning-goal aggregate assumed.'}
(owner/'accounting.json').write_text(json.dumps(accounting,indent=2)+'\n')
print(json.dumps({'review_sessions':list(sessions),'review_observed_usage':observed,'accounting_status':accounting['status']}))
