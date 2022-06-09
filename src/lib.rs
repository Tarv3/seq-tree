use std::{collections::VecDeque, marker::PhantomData};

#[derive(Clone, Copy, Debug)]
pub enum TreeAppendError {
    MissingParent { parent: usize, child: usize },
    AlreadyChild { child: usize },
}

impl std::error::Error for TreeAppendError {}

impl std::fmt::Display for TreeAppendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TreeAppendError::MissingParent { parent, child } => {
                write!(f, "Missing parent {} for child {}", parent, child)
            }
            TreeAppendError::AlreadyChild { child } => {
                write!(f, "Node {} is already a child", child)
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Node<T> {
    pub data: T,
    parent: Option<usize>,
    r_sibling: Option<usize>,
    l_sibling: Option<usize>,
    children: usize,
    child: Option<usize>,
}

impl<T> Node<T> {
    pub fn new(data: T) -> Self {
        Self {
            data,
            parent: None,
            r_sibling: None,
            l_sibling: None,
            children: 0,
            child: None,
        }
    }

    pub fn parent(&self) -> Option<usize> {
        self.parent
    }

    pub fn child(&self) -> Option<usize> {
        self.child
    }

    pub fn children(&self) -> usize {
        self.children
    }

    pub fn is_first_child(&self) -> bool {
        self.parent.is_some() && self.l_sibling.is_none()
    }

    pub fn add_offset(&mut self, offset: usize) {
        if let Some(parent) = &mut self.parent {
            *parent += offset;
        }

        if let Some(r_sibling) = &mut self.r_sibling {
            *r_sibling += offset;
        }

        if let Some(l_sibling) = &mut self.l_sibling {
            *l_sibling += offset;
        }

        if let Some(child) = &mut self.child {
            *child += offset;
        }
    }

    pub fn handle_remove(&mut self, removed: usize) {
        let remove = |value: &mut Option<usize>| {
            if let Some(value) = value {
                if *value > removed {
                    *value -= 1;
                }
            }
        };

        remove(&mut self.parent);
        remove(&mut self.r_sibling);
        remove(&mut self.l_sibling);
        remove(&mut self.child);
    }
}

#[derive(Clone, Debug)]
pub struct SeqTree<T> {
    roots: Vec<usize>,
    nodes: Vec<Node<T>>,
}

impl<T> SeqTree<T> {
    pub fn new() -> Self {
        Self {
            roots: vec![],
            nodes: vec![],
        }
    }

    pub fn clear(&mut self) {
        self.nodes.clear();
    }

    pub fn roots(&self) -> &[usize] {
        &self.roots
    }

    pub fn nodes(&self) -> &[Node<T>] {
        &self.nodes
    }

    pub fn nodes_mut(&mut self) -> &mut [Node<T>] {
        &mut self.nodes
    }

    pub fn append(&mut self, mut tree: SeqTree<T>) {
        let offset = self.nodes.len();

        for mut node in tree.nodes.drain(..) {
            if node.parent.is_none() {
                self.roots.push(self.nodes.len());
            }

            node.add_offset(offset);
            self.nodes.push(node);
        }
    }

    pub fn append_with_parent(
        &mut self,
        mut tree: SeqTree<T>,
        parented: impl IntoIterator<Item = (usize, usize)>,
    ) -> Result<(), TreeAppendError> {
        let offset = self.nodes.len();

        for mut node in tree.nodes.drain(..) {
            node.add_offset(offset);
            self.nodes.push(node);
        }

        for (parent_id, child) in parented.into_iter() {
            let id = child + offset;

            if parent_id >= offset {
                self.nodes.truncate(offset);

                return Err(TreeAppendError::MissingParent {
                    parent: parent_id,
                    child,
                });
            }

            if self.nodes[id].parent.is_some() {
                self.nodes.truncate(offset);
                return Err(TreeAppendError::AlreadyChild { child });
            }

            let parent = &mut self.nodes[parent_id];
            let r_sibling = parent.child;
            parent.children += 1;
            parent.child = Some(id);

            if let Some(r_sibling) = r_sibling {
                self.nodes[r_sibling].l_sibling = Some(id);
            }

            self.nodes[id].parent = Some(parent_id);
            self.nodes[id].r_sibling = r_sibling;
        }

        for id in offset..self.nodes.len() {
            if self.nodes[id].parent.is_none() {
                self.roots.push(id);
            }
        }

        Ok(())
    }

    /// If the parent does not exist, Err(data) is returned otherwise Ok(id) is returned.
    pub fn insert(&mut self, data: T, parent: Option<usize>) -> Result<usize, T> {
        let mut node = Node::new(data);
        let id = self.nodes.len();

        if let Some(parent) = parent {
            let parent = match self.nodes.get_mut(parent) {
                Some(parent) => parent,
                None => return Err(node.data),
            };

            let r_sibling = parent.child;
            parent.children += 1;
            parent.child = Some(id);
            node.r_sibling = r_sibling;

            if let Some(r_sibling) = r_sibling {
                self.nodes[r_sibling].l_sibling = Some(id);
            }
        }

        node.parent = parent;
        self.nodes.push(node);
        if parent.is_none() {
            self.roots.push(id);
        }

        Ok(id)
    }

    /// Removes the node with the given id. All ids after 'id' must be shifted by -1 to point to the
    /// correct data.
    pub fn remove(&mut self, id: usize) -> Option<T> {
        if id >= self.nodes.len() {
            return None;
        }

        if self.nodes[id].parent.is_none() {
            self.roots.retain(|value| *value != id);
        }

        for root in self.roots.iter_mut() {
            if *root > id {
                *root -= 1;
            }
        }

        // make all child nodes of the removed node a root
        let mut child = self.nodes[id].child;

        while let Some(idx) = child {
            self.roots.push(idx - 1);
            let node = &mut self.nodes[idx];
            child = node.r_sibling;
            node.parent = None;
            node.r_sibling = None;
            node.l_sibling = None;
        }

        // Fix the removed nodes siblings and parent
        let r_sibling = self.nodes[id].r_sibling;
        let l_sibling = self.nodes[id].l_sibling;
        let parent = self.nodes[id].parent;

        if let Some(l) = l_sibling {
            self.nodes[l].r_sibling = r_sibling;
            if let Some(r) = r_sibling {
                self.nodes[r].l_sibling = Some(l);
            }
        } else if let Some(parent) = parent {
            self.nodes[parent].child = r_sibling;
            if let Some(r) = r_sibling {
                self.nodes[r].l_sibling = None;
            }
        }

        if let Some(parent) = parent {
            self.nodes[parent].children -= 1;
        }

        // Fix all nodes to the right of this node as they will be shifted back by one
        for i in id + 1..self.nodes.len() {
            // If this next node is the first child, the parent may need to have their child idx
            // changed
            if self.nodes[i].is_first_child() {
                let parent = self.nodes[i].parent.unwrap();
                // If parent > id, this will be fixed in this loop so we skip
                if parent < id {
                    *self.nodes[parent].child.as_mut().unwrap() -= 1;
                }
            }

            self.nodes[i].handle_remove(id);
        }

        Some(self.nodes.remove(id).data)
    }

    pub fn iter_children(&self, node: usize) -> ChildIter<T> {
        match self.nodes.get(node) {
            Some(node) => ChildIter {
                tree: self,
                current: node.child,
            },
            None => ChildIter {
                tree: self,
                current: None,
            },
        }
    }

    pub fn iter_all_children(&self, node: usize) -> AllChildIter<T> {
        match self.nodes.get(node) {
            Some(node) if node.child.is_some() => AllChildIter::new(self, node.child.unwrap()),
            _ => AllChildIter::empty(self),
        }
    }

    pub fn iter_children_idx(&self, node: usize) -> ChildIdxIter<T> {
        match self.nodes.get(node) {
            Some(node) => ChildIdxIter {
                tree: self,
                current: node.child,
            },
            None => ChildIdxIter {
                tree: self,
                current: None,
            },
        }
    }

    pub fn iter_children_mut(&mut self, node: usize) -> ChildIterMut<T> {
        match self.nodes.get(node).map(|node| node.child) {
            Some(child) => ChildIterMut::new(self, child),
            None => ChildIterMut::new(self, None),
        }
    }

    pub fn iter_parents(&self, node: usize) -> ParentIter<T> {
        match self.nodes.get(node) {
            Some(node) => ParentIter {
                tree: self,
                current: node.parent,
            },
            None => ParentIter {
                tree: self,
                current: None,
            },
        }
    }

    pub fn iter_parents_mut(&mut self, node: usize) -> ParentIterMut<T> {
        match self.nodes.get(node).map(|node| node.parent) {
            Some(parent) => ParentIterMut::new(self, parent),
            None => ParentIterMut::new(self, None),
        }
    }
}

pub struct ChildIter<'a, T> {
    tree: &'a SeqTree<T>,
    current: Option<usize>,
}

impl<'a, T> Iterator for ChildIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        let node = self.tree.nodes.get(current)?;
        self.current = node.r_sibling;

        Some(&node.data)
    }
}

pub struct ChildIdxIter<'a, T> {
    tree: &'a SeqTree<T>,
    current: Option<usize>,
}

impl<'a, T> Iterator for ChildIdxIter<'a, T> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        let node = self.tree.nodes.get(current)?;
        self.current = node.r_sibling;

        Some(current)
    }
}

pub struct AllChildIter<'a, T> {
    tree: &'a SeqTree<T>,
    remaining: VecDeque<usize>,
}

impl<'a, T> AllChildIter<'a, T> {
    pub fn new(tree: &'a SeqTree<T>, first: usize) -> Self {
        let mut queue = VecDeque::new();
        queue.push_back(first);

        Self {
            tree,
            remaining: queue,
        }
    }

    pub fn empty(tree: &'a SeqTree<T>) -> Self {
        Self {
            tree,
            remaining: VecDeque::new(),
        }
    }
}

impl<'a, T> Iterator for AllChildIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let first = self.remaining.pop_front()?;
        let node = self.tree.nodes.get(first)?;

        for child in self.tree.iter_children_idx(first) {
            self.remaining.push_back(child);
        }

        Some(&node.data)
    }
}

pub struct ChildIterMut<'a, T> {
    ptr: *mut Node<T>,
    current: Option<usize>,
    _phantom: PhantomData<&'a mut T>,
}

impl<'a, T> ChildIterMut<'a, T> {
    pub fn new(tree: &'a mut SeqTree<T>, current: Option<usize>) -> Self {
        let ptr = tree.nodes.as_mut_ptr();

        Self {
            ptr,
            current,
            _phantom: PhantomData,
        }
    }
}

impl<'a, T> Iterator for ChildIterMut<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        // SAFETY: We ensure that siblings are always placed in reversed.
        let node = unsafe { &mut *self.ptr.add(current) };

        // This should never happen if the data structure is created properly, children are always
        // placed after their r_sibling.
        // Ensures we never return multiple mutable reference to the same data
        if let Some(next) = node.r_sibling {
            assert!(next < current);
        }

        self.current = node.r_sibling;
        Some(&node.data)
    }
}

pub struct ParentIter<'a, T> {
    tree: &'a SeqTree<T>,
    current: Option<usize>,
}

impl<'a, T> Iterator for ParentIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        let node = self.tree.nodes.get(current)?;
        self.current = node.parent;

        Some(&node.data)
    }
}

pub struct ParentIterMut<'a, T> {
    ptr: *mut Node<T>,
    current: Option<usize>,
    _phantom: PhantomData<&'a mut T>,
}

impl<'a, T> ParentIterMut<'a, T> {
    pub fn new(tree: &'a mut SeqTree<T>, current: Option<usize>) -> Self {
        let ptr = tree.nodes.as_mut_ptr();

        Self {
            ptr,
            current,
            _phantom: PhantomData,
        }
    }
}

impl<'a, T> Iterator for ParentIterMut<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current?;
        let node = unsafe { &mut *self.ptr.add(current) };

        // This should never happen if the data structure is created properly, children are always
        // placed after their parents.
        // Ensures we never return multiple mutable reference to the same data
        if let Some(next) = node.parent {
            assert!(next < current);
        }

        self.current = node.parent;
        Some(&node.data)
    }
}

#[cfg(test)]
mod tests {
    use crate::SeqTree;

    #[test]
    fn test_insert() {
        let mut tree = SeqTree::new();
        let id_0 = tree.insert(0, None).unwrap();
        tree.insert(1, Some(id_0)).unwrap();
        tree.insert(2, Some(id_0)).unwrap();
        tree.insert(3, Some(id_0)).unwrap();

        let id_4 = tree.insert(4, None).unwrap();
        let id_5 = tree.insert(5, Some(id_4)).unwrap();
        let id_6 = tree.insert(6, Some(id_5)).unwrap();

        let mut id_0_children = tree.iter_children(id_0);
        assert_eq!(id_0_children.next(), Some(&3));
        assert_eq!(id_0_children.next(), Some(&2));
        assert_eq!(id_0_children.next(), Some(&1));
        assert_eq!(id_0_children.next(), None);

        let mut id_4_children = tree.iter_children(id_4);
        assert_eq!(id_4_children.next(), Some(&5));
        assert_eq!(id_4_children.next(), None);

        let mut id_5_children = tree.iter_children(id_5);
        assert_eq!(id_5_children.next(), Some(&6));
        assert_eq!(id_5_children.next(), None);

        let mut id_6_parents = tree.iter_parents(id_6);
        assert_eq!(id_6_parents.next(), Some(&5));
        assert_eq!(id_6_parents.next(), Some(&4));
        assert_eq!(id_6_parents.next(), None);

        assert_eq!(tree.roots.as_slice(), &[0, 4]);
    }

    #[test]
    fn test_remove() {
        let mut tree = SeqTree::new();
        let id_0 = tree.insert(0, None).unwrap();
        tree.insert(1, Some(id_0)).unwrap();
        tree.insert(2, Some(id_0)).unwrap();
        tree.insert(3, Some(id_0)).unwrap();

        let id_4 = tree.insert(4, None).unwrap();
        let id_5 = tree.insert(5, Some(id_4)).unwrap();
        let id_6 = tree.insert(6, Some(id_5)).unwrap();

        assert_eq!(tree.remove(1), Some(1));
        assert_eq!(tree.remove(4), Some(5));

        let mut id_0_children = tree.iter_children(id_0);
        assert_eq!(id_0_children.next(), Some(&3));
        assert_eq!(id_0_children.next(), Some(&2));
        assert_eq!(id_0_children.next(), None);
        assert_eq!(tree.nodes[0].children, 2);

        let mut id_4_children = tree.iter_children(id_4 - 1);
        assert_eq!(id_4_children.next(), None);
        assert_eq!(tree.nodes[3].children, 0);

        let mut id_6_parents = tree.iter_parents(id_6 - 2);
        assert_eq!(id_6_parents.next(), None);

        assert_eq!(tree.roots.as_slice(), &[0, 3, 4]);
    }

    #[test]
    fn test_append() {
        let mut tree = SeqTree::new();
        let id_0 = tree.insert(0, None).unwrap();
        tree.insert(1, Some(id_0)).unwrap();
        tree.insert(2, Some(id_0)).unwrap();
        tree.insert(3, Some(id_0)).unwrap();

        let id_4 = tree.insert(4, None).unwrap();
        let id_5 = tree.insert(5, Some(id_4)).unwrap();
        tree.insert(6, Some(id_5)).unwrap();

        let cloned = tree.clone();
        tree.append(cloned);
        assert_eq!(tree.roots.as_slice(), &[0, 4, 7, 11]);

        let mut id_7_children = tree.iter_children(7);
        assert_eq!(id_7_children.next(), Some(&3));
        assert_eq!(id_7_children.next(), Some(&2));
        assert_eq!(id_7_children.next(), Some(&1));
        assert_eq!(id_7_children.next(), None);

        let mut id_11_children = tree.iter_children(11);
        assert_eq!(id_11_children.next(), Some(&5));
        assert_eq!(id_11_children.next(), None);

        let mut id_12_children = tree.iter_children(12);
        assert_eq!(id_12_children.next(), Some(&6));
        assert_eq!(id_12_children.next(), None);

        let mut id_12_parents = tree.iter_parents(13);
        assert_eq!(id_12_parents.next(), Some(&5));
        assert_eq!(id_12_parents.next(), Some(&4));
        assert_eq!(id_12_parents.next(), None);
    }

    #[test]
    fn test_append_with_parents() {
        let mut tree = SeqTree::new();
        let id_0 = tree.insert(0, None).unwrap();
        tree.insert(1, Some(id_0)).unwrap();
        tree.insert(2, Some(id_0)).unwrap();
        tree.insert(3, Some(id_0)).unwrap();

        let id_4 = tree.insert(4, None).unwrap();
        let id_5 = tree.insert(5, Some(id_4)).unwrap();
        tree.insert(6, Some(id_5)).unwrap();

        let cloned = tree.clone();
        tree.append_with_parent(cloned, [(id_0, id_4)]).unwrap();
        assert_eq!(tree.roots.as_slice(), &[0, 4, 7]);

        let mut id_0_children = tree.iter_children(id_0);
        assert_eq!(id_0_children.next(), Some(&4));
        assert_eq!(id_0_children.next(), Some(&3));
        assert_eq!(id_0_children.next(), Some(&2));
        assert_eq!(id_0_children.next(), Some(&1));
        assert_eq!(id_0_children.next(), None);

        let mut id_7_children = tree.iter_children(7);
        assert_eq!(id_7_children.next(), Some(&3));
        assert_eq!(id_7_children.next(), Some(&2));
        assert_eq!(id_7_children.next(), Some(&1));
        assert_eq!(id_7_children.next(), None);

        let mut id_11_children = tree.iter_children(11);
        assert_eq!(id_11_children.next(), Some(&5));
        assert_eq!(id_11_children.next(), None);

        let mut id_12_children = tree.iter_children(12);
        assert_eq!(id_12_children.next(), Some(&6));
        assert_eq!(id_12_children.next(), None);

        let mut id_12_parents = tree.iter_parents(12);
        assert_eq!(id_12_parents.next(), Some(&4));
        assert_eq!(id_12_parents.next(), Some(&0));
        assert_eq!(id_12_parents.next(), None);

        let mut id_13_parents = tree.iter_parents(13);
        assert_eq!(id_13_parents.next(), Some(&5));
        assert_eq!(id_13_parents.next(), Some(&4));
        assert_eq!(id_13_parents.next(), Some(&0));
        assert_eq!(id_13_parents.next(), None);
    }
}
