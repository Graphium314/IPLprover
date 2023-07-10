'''
入力に用いる命題は、以下の規則に沿っている必要がある
そうでない場合の動作は未定義

原子命題:(文字列)
含意:(命題1->命題2)
連言:(命題1/\命題2)
選言:(命題1\/命題2)
否定:(~命題) (内部では(命題->(False))と表現されている)

これらは、listを用いて以下のように表される
(A):[A]  (A:string)
(A->B):[0,A,B]
(A/\B):[1,A,B]
(A\/B):[2,A,B]

ε_(A):False型を受け取り、型Aを返す関数(不条理則)
'''




class prover:
  '''証明器クラス'''

  def __init__(self):
    self.lt = 0  # 変数のナンバリング用
    self.prooving = []  # [示す命題, 仮定]の組を持ち、再帰関数でのループを検出

  def ltos(self,a):
    '''
    配列で表現された命題を文字列に変換
    '''
    if a[0] == 0:
      if a[2] == ['False']:
        return f'(~{self.ltos(a[1])})'
      return '(' + self.ltos(a[1]) + '->' + self.ltos(a[2]) + ')'
    elif a[0] == 1:
      return '(' + self.ltos(a[1]) + '/\\' + self.ltos(a[2]) + ')'
    elif a[0] == 2:
      return '(' + self.ltos(a[1]) + '\\/' + self.ltos(a[2]) + ')'
    else:
      return f'({a[0]})'


  def stol(self,s):
    '''
    文字列で表現された命題を配列に変換
    '''
    if s.count('(') == 1:
      return [s[1:-1]]
    if(s[1] == '~'):
      return [0, self.stol(s[2:-1]), ['False']]
    n = len(s)
    c = 0
    for i in range(1, n-1):
      if s[i] == '(':
        c += 1
      elif s[i] == ')':
        c -= 1
      if c == 0:
        m = {'->': 0, '/\\': 1, '\\/': 2, }
        return [m[s[i+1:i+3]], self.stol(s[1:i+1]), self.stol(s[i+3:n-1])]
  def reset(self):
    '''初期化'''
    self.lt = 0
    self.prooving = []

  def contain(self, p, a):
    if a == p or p == ['False']:
      return True
    elif p[0] == 0:
      return self.contain(p[2], a)
    elif p[0] == 1 or p[0] == 2:
      return self.contain(p[1], a) or self.contain(p[2], a)
    return False

  def split(self, a, x, d):
    '''
    λ式xで表される命題aを受け取ってdに登録し、aが連言である場合には、それぞれも登録
    Parameters
    ----------
    a : list
      命題(型)を表現
    x : string
      aの証明となるλ式
    d : dict
      命題をkey,そのλ式をvalueとして仮定を保存
    '''
    if a[0] == 1:
      self.split(a[1], f'fst({x})', d)
      self.split(a[2], f'snd({x})', d)
    else:
      if not self.ltos(a) in d:
        d[self.ltos(a)] = x

  def proof(self, a):
    '''
    命題aを証明するλ式を返す
    Parameters
    ----------
    a : list
      命題(型)を表現
    '''
    self.reset()  # 初期化
    d = dict()  # 仮定を保存するdictを用意
    return self.prove(self.stol(a), d)  # 再帰関数で証明する

  def prove(self, a, d):
    '''
    命題aを証明するλ式を返す
    proofによって呼び出し、直に呼び出さない
    Parameters
    ----------
    a : list
      命題(型)を表現
    d : dict
      命題をkey,そのλ式をvalueとして仮定を保存
    '''
    # print(a,d)
    if [a, d] in self.prooving:  # 無限ループ防止
      return 'No'
    self.prooving.append([a.copy(), d.copy()])

    if self.ltos(a) in d:  # 仮定に証明が含まれていれば、それを返す
      self.prooving.pop(-1)
      return d[self.ltos(a)]
    if '(False)' in d:
      self.prooving.pop(-1)
      mujun = d['(False)']
      return f'(ε_{self.ltos(a)} {mujun})'

    if a[0] == 0:  # A->Bを示す場合、Aをdに登録し、Bを示す
      lt1 = self.lt
      self.lt += 1
      dd = d.copy()
      self.split(a[1], f'x{lt1}', dd)
      pr = self.prove(a[2], dd)
      if pr == 'No':
        self.prooving.pop(-1)
        return 'No'
      self.prooving.pop(-1)
      return f'(λx{lt1}:{self.ltos(a[1])}. {pr})'
    elif a[0] == 1:  # A/\Bを示す場合、AとBのそれぞれの証明を探索し、その組を返す
      pr1 = self.prove(a[1], d)
      pr2 = self.prove(a[2], d)
      if pr1 == 'No' or pr2 == 'No':
        self.prooving.pop(-1)
        return 'No'
      self.prooving.pop(-1)
      return f'({pr1}, {pr2})'
    elif a[0] == 2:  # A\/Bを示す場合、AとBのそれぞれの証明を探索し、片方を返す
      pr1 = self.prove(a[1], d)
      pr2 = self.prove(a[2], d)
      if pr1 != 'No':
        self.prooving.pop(-1)
        return f'inl({pr1})'
      if pr2 == 'No':
        self.prooving.pop(-1)
        return 'No'
      self.prooving.pop(-1)
      return f'inr({pr2})'
    else:  # 原子命題の場合
      dd = d.copy()
      while True:
        for j in dd.keys():  # 関数適用を用いて、仮定を増やす
          i = self.stol(j)
          if i[0] != 0:
            continue
          if not self.contain(i[2], a):
            continue
          s = self.prove(i[1], d)
          if s != 'No':
            self.split(i[2], f'({d[self.ltos(i)]} {s})', d)
        if len(d) == len(dd):  # 仮定が増えなかったらループを終了する
          break
        if self.ltos(a) in d:  # 仮定に証明が含まれていれば、それを返す
          self.prooving.pop(-1)
          return d[self.ltos(a)]
        if '(False)' in d:
          self.prooving.pop(-1)
          mujun = d['(False)']
          return f'(ε_{self.ltos(a)} {mujun})'
        dd = d.copy()
      for j in d.keys():  # 選言の場合分け
        i = self.stol(j)
        if i[0] != 2:
          continue
        d1 = d.copy()
        lt1 = self.lt
        self.split(i[1], f'x{lt1}', d1)
        d2 = d.copy()
        self.split(i[2], f'x{lt1+1}', d2)
        self.lt += 2
        p1 = self.prove(a, d1)
        p2 = self.prove(a, d2)
        if p1 != 'No' and p2 != 'No':
          self.prooving.pop(-1)
          return f'(case {d[j]} of inl(x{lt1}) => {p1} | inr(x{lt1+1}) => {p2})'
      self.prooving.pop(-1)
      return 'No'