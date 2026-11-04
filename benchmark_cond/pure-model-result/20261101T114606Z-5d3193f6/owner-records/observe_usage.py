"""Read-only native usage observation; never sum cumulative snapshots."""
import datetime,json,pathlib
root=pathlib.Path(__file__).resolve().parent.parent
owner=root/'owner-records'
sessions={}
for path in (root/'native-home/sessions').rglob('*.jsonl'):
    current=None
    for line in path.open():
        try: event=json.loads(line)
        except json.JSONDecodeError: continue
        payload=event.get('payload',{})
        if event.get('type')=='session_meta': current=payload.get('id')
        if event.get('type')!='event_msg' or payload.get('type')!='token_count': continue
        info=payload.get('info') or {}; usage=info.get('total_token_usage')
        if not usage: continue
        key=current or str(path)
        prior=sessions.get(key)
        if prior and usage.get('total_tokens',0)<prior['usage'].get('total_tokens',0):
            raise RuntimeError('Cumulative usage decreased; manual reset/baseline audit required')
        sessions[key]={'path':str(path),'timestamp':event.get('timestamp'),'ordinal':event.get('ordinal'),'usage':usage}
allowed='01a196f3-4972-7951-ac8d-0a7cc1b7e244'
assert set(sessions).issubset({allowed}), 'Unexpected measured author session; inspect before aggregation'
author=sessions.get(allowed,{}).get('usage',{})
fields=('input_tokens','cached_input_tokens','output_tokens','reasoning_output_tokens','total_tokens')
observed={key:author.get(key) for key in fields}
accounting=json.loads((owner/'accounting.json').read_text())
accounting['observed_at_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
accounting['supplement']['author_observed_usage']=observed
accounting['supplement']['usage']='Latest cumulative native session snapshot, baseline zero for fresh session; cached/reasoning are subsets. Unfinished last response may be missing.'
accounting['supplement']['raw_snapshot_receipt']=sessions
if all(observed.get(k) is not None for k in ('input_tokens','output_tokens')):
    accounting['combined_observed_total']={'input_tokens':190088829+observed['input_tokens'],'output_tokens':861602+observed['output_tokens'],'input_plus_output_tokens':190950431+observed['input_tokens']+observed['output_tokens'],'scope':'Historical original plus observed author supplement so far; unexposed operator/provider/account usage remains PARTIAL, not zero'}
(owner/'accounting.json').write_text(json.dumps(accounting,indent=2))
print(json.dumps({'author_observed_usage':observed,'accounting_status':'PARTIAL_RUNNING'}))
