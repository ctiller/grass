import pathlib, subprocess, re, hashlib, json, csv
base = pathlib.Path('C:/Users/craig/.codex/worktrees')
roots = [('main',base/'8896/grass'),('certificate',base/'grass-certificate-root'),('frontend',base/'8509/grass'),('lowering',base/'0a71/grass'),('windows',base/'a25b/grass'),('process',base/'grass-execution-steps')]
out = pathlib.Path('docs/audits/hello-specialization')
out.mkdir(parents=True,exist_ok=True)
pattern = re.compile(r'hello|spike[ _./-]?1|1_Hello_World',re.I)
decl = re.compile(r'^\s*(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(def|theorem|structure|inductive|abbrev|opaque|axiom)\s+([^\s(:{]+)')
prefixes = ('Grass/Frontend/','Grass/Console/','Grass/Refinement/Console/','Grass/Std/Console/','Grass/Platform/Win32/','Tests/Frontend/','Tests/Platform/','Tests/Console/','Tests/Assembly/','Grass/Assembly/')
rows, declarations, hits, snapshots = [],[],[],[]
seen = {}
for label,root in roots:
 def git(*args): return subprocess.check_output(['git','-C',str(root),*args]).decode('utf-8',errors='replace')
 snapshots.append(dict(label=label,path=str(root),head=git('rev-parse','HEAD').strip(),status=git('status','--short')))
 paths=git('ls-files','--cached','--others','--exclude-standard').splitlines()
 scanned=0
 for path in sorted(set(paths)):
  if path.startswith(('docs/audits/hello-specialization/','.lake/')) or path=='census-search.txt': continue
  file=root/path
  if not file.is_file() or file.stat().st_size>2000000: continue
  if file.suffix.lower() not in ('.lean','.in','.sh','.ps1','.py','.rs','.toml','.yml','.yaml','.md'): continue
  try: content=file.read_text(encoding='utf-8-sig')
  except UnicodeError: continue
  scanned+=1
  matches=[(i,line) for i,line in enumerate(content.splitlines(),1) if pattern.search(line)]
  selected=bool(matches) or path.startswith(prefixes)
  if not selected: continue
  digest=hashlib.sha256(content.encode()).hexdigest()
  key=(path,digest)
  if key in seen:
   seen[key]['trees']+=','+label
   continue
  row=dict(path=path,trees=label,sha256=digest,lines=len(content.splitlines()),reason='text-match' if matches else 'semantic-boundary-or-consumer',text_hits=len(matches))
  rows.append(row);seen[key]=row
  for i,line in matches: hits.append(dict(path=path,variant=digest[:12],line=i,text=line.strip()))
  for i,line in enumerate(content.splitlines(),1):
   m=decl.match(line)
   if m: declarations.append(dict(path=path,variant=digest[:12],line=i,kind=m[1],name=m[2]))
 snapshots[-1]['text_files_scanned']=scanned
for name,data in [('files',rows),('declarations',declarations),('text-matches',hits)]:
 with (out/(name+'.tsv')).open('w',encoding='utf-8',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=list(data[0]),delimiter='\t');writer.writeheader();writer.writerows(data)
(out/'snapshots.json').write_text(json.dumps(snapshots,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(file_variants=len(rows),paths=len(set(r['path'] for r in rows)),lexical_declarations=len(declarations),text_hits=len(hits),snapshots=snapshots),indent=2))
