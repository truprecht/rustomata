#[derive(PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct StateStorage<N> {
    inner: Vec<Option<(u8, N)>>,
}

impl<N> StateStorage<N> {
    pub fn with_capacity(c: usize) -> Self
    where
        N: Clone,
    {
        StateStorage {
            inner: vec![None; c],
        }
    }

    pub fn get(&self, index: u32) -> Option<(u8, &N)> {
        if let &Some((comp, ref n)) = &self.inner[index as usize] {
            Some((comp, n))
        } else {
            None
        }
    }
}

impl<N> ::std::ops::Index<u32> for StateStorage<N> {
    type Output = Option<(u8, N)>;
    fn index(&self, index: u32) -> &Self::Output {
        &self.inner[index as usize]
    }
}

impl<N> ::std::ops::IndexMut<u32> for StateStorage<N> {
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        &mut self.inner[index as usize]
    }
}
