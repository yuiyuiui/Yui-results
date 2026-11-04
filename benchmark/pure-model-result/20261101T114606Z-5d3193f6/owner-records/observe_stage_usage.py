"""Passive interval and cumulative-delta accounting; never sum snapshots."""
import datetime,json,pathlib
root=pathlib.Path(__file__).resolve().parent.parent
owner=root/'owner-records'
fields=('input_tokens','cached_input_tokens','output_tokens','reasoning_output_tokens','total_tokens')
def stamp(s):return datetime.datetime.fromisoformat(s.replace('Z','+00:00'))
now=datetime.datetime.now(datetime.timezone.utc)
roles={}
for role,home,session in [('author','native-home','01a196f3-4972-7951-ac8d-0a7cc1b7e244'),('review','review-001-home','01a197b1-0aeb-7fd1-b6d4-f1f63aab268a')]:
    rows=[]
    for path in (root/home/'sessions').rglob('*'+session+'.jsonl'):
        for line in path.open():
            try:e=json.loads(line)
            except json.JSONDecodeError:continue
            p=e.get('payload',{})
            if e.get('type')!='event_msg' or p.get('type')!='token_count':continue
            u=(p.get('info') or {}).get('total_token_usage')
            if u:rows.append({'timestamp':e['timestamp'],'usage':u,'path':str(path),'ordinal':e.get('ordinal')})
    rows.sort(key=lambda z:stamp(z['timestamp']))
    for a,b in zip(rows,rows[1:]):
        assert b['usage']['total_tokens']>=a['usage']['total_tokens'], 'Cumulative decrease; manual baseline audit required'
    prior={k:0 for k in fields};stages=[]
    for process in sorted(owner.glob(role+'-*-process.json')):
        record=json.loads(process.read_text());n=record['turn'];exitfile=owner/(role+f'-{n:03d}-exit.json')
        terminal=exitfile.exists();end=json.loads(exitfile.read_text()) if terminal else None
        cutoff=stamp(end['end_utc']) if terminal else now
        eligible=[z for z in rows if stamp(z['timestamp'])<=cutoff]
        latest=eligible[-1] if eligible else None
        usage={k:latest['usage'].get(k) for k in fields} if latest else {k:None for k in fields}
        delta={k:usage[k]-prior[k] if usage[k] is not None and prior[k] is not None else None for k in fields}
        assert all(v is None or v>=0 for v in delta.values())
        stages.append({'turn':n,'start_utc':record['start_utc'],'end_utc':end['end_utc'] if terminal else None,'terminal':terminal,'elapsed_seconds':end['elapsed_seconds'] if terminal else (now-stamp(record['start_utc'])).total_seconds(),'exit_code':end['exit_code'] if terminal else None,'baseline_cumulative_usage':prior,'latest_cumulative_usage':usage,'observed_stage_delta':delta,'snapshot':latest})
        prior=usage
    roles[role]={'session':session,'home':home,'stages':stages,'interval_sum_seconds_observed':sum(z['elapsed_seconds'] for z in stages),'latest_cumulative_usage':prior}
start=json.loads((owner/'measurement-start.json').read_text())['operator_interval_start_utc']
record={'observed_at_utc':now.isoformat(),'status':'PARTIAL','roles':roles,'supplement_end_to_end_wall_seconds_observed':(now-stamp(start)).total_seconds(),'notes':['Each fresh session has baseline zero. Per-stage delta uses the latest native cumulative usage at or before the actual turn exit; resumed stages subtract the preceding terminal cumulative baseline.','Cached input and reasoning output are subsets, never added to input+output.','Running generation may be absent from the latest token_count snapshot. All source, self-check, ordinary compiler repair and tool retry tokens remain in the native session totals; semantic subphase token splits are not exposed.','Owner aggregate goal tokens and unexposed provider/account or earlier setup usage are separate PARTIAL/UNVERIFIED categories, not zero and not silently summed.','Author/review interval sums and supplement end-to-end wall are distinct measures. Do not sum overlapping waits with wall time.','Deleted cancelled attempts have unavailable all-history costs; no reconstruction.']}
(owner/'native-stage-usage.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({role:{'stages':len(v['stages']),'interval_sum_seconds_observed':v['interval_sum_seconds_observed'],'latest_total_tokens':v['latest_cumulative_usage'].get('total_tokens')} for role,v in roles.items()}))
