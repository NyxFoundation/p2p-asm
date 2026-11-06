import unittest
from oracle import Receive, MAX

class ReceiveTests(unittest.TestCase):
    def test_should_charge_highest_offset_when_gaps_and_duplicates_arrive(self):
        e,s,d = Receive().put(3, b'def')
        self.assertEqual((e,d,s.peek()), (0,6,(0,0)))
        e,s,d = s.put(0,b'abc')
        self.assertEqual((e,d,s.peek()), (0,0,(0,6)))
        self.assertEqual(s.put(2,b'cde')[2], 0)

    def test_should_reject_conflict_without_publication(self):
        _,s,_ = Receive().put(3,b'def')
        e,t,d = s.put(0,b'abcXef')
        self.assertEqual((e,t,d), (5,s,0))

    def test_should_charge_zero_length_and_reset_final_size(self):
        e,s,d = Receive().put(100,b'')
        self.assertEqual((e,d), (0,100))
        e,s,d = s.put(103,b'',2)
        self.assertEqual((e,d,s.final,s.reset), (0,3,103,1))
        self.assertEqual(s.put(103,b'',2)[2], 0)
        self.assertEqual(s.put(102,b'',1)[0], 4)

    def test_should_retain_suffix_and_wrap_after_consumption(self):
        _,s,_ = Receive().put(0,b'abcdefgh')
        _,s = s.consume(6)
        _,s,_ = s.put(8,b'ijklmn')
        self.assertEqual(s.peek(), (6,2))
        _,s = s.consume(2)
        self.assertEqual(s.peek(), (0,6))

    def test_should_separate_lifetime_offsets_from_crypto_capacity(self):
        e,s,d = Receive(base=MAX-3, highest=MAX-3, crypto=1).put(MAX-3,b'abc')
        self.assertEqual((e,d), (0,0))
        self.assertEqual(s.put(MAX,b'a')[0], 2)
        self.assertEqual(Receive(crypto=1).put(9,b'x')[0], 7)

if __name__ == '__main__':
    unittest.main()
