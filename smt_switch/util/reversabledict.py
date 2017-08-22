class reversabledict:
    '''
       Dict that can be reversed with ~ operator

       Borrowed heavily from:
         https://pypi.python.org/pypi/bidict
         and 
         https://github.com/cdonovick/SMT-PNR/blob/master/pnrdoctor/util/data_structures/bidict.py

       Implemented here to avoid additional dependencies
    '''
    def __init__(self, d=dict()):
        self._d = dict()
        self._r = dict()

        for key, val in d.items():
            self[key] = val
        
    def __getitem__(self, key):
        return self._d[key]

    def __setitem__(self, key, value):
        self._d[key] = value
        self._r[value] = key

    def __delitem__(self, key):
        del self._d[key]

    @property
    def rev(self):
        rd = reversabledict()
        rd._d = self._r
        rd._r = self._d
        return rd

    def __len__(self):
        return len(self._d)

    def __iter__(self):
        yield from self._d.keys()

    def __repr__(self):
        l = []
        for key, val in self._d.items():
            l.append('{}: {}'.format(key, val))

        inter_s = ', '.join(l)
        return '<reversabledict {}>'.format(inter_s)
