package org.exactlearner.ui;

import java.awt.EventQueue;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.ArrayList;

import javax.swing.AbstractListModel;
import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.border.EmptyBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

public class LoadFromList extends JFrame {

	private JPanel contentPane;

	private ArrayList<String> ontologies = new ArrayList<String>();
	private JList<Object> ontologyList = new JList<Object>(); 
	/**
	 * Launch the application.
	 */
	public static void main(String[] args) {
		EventQueue.invokeLater(new Runnable() {
			public void run() {
				try {
					LoadFromList frame = new LoadFromList();
					frame.setVisible(true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
	}

	/**
	 * Create the frame.
	 */
	public LoadFromList() {
		super();
		ontologies.add("src/main/resources/ontologies/SMALL/football.owl");
		ontologies.add("src/main/resources/ontologies/SMALL/university.owl");
		ontologies.add("src/main/resources/ontologies/SMALL/animals.owl");
		ontologies.add("src/main/resources/ontologies/SMALL/generations.owl");
		
		setTitle("ExactLearner - Load from list");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setBounds(100, 100, 396, 213);
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);
		JList list = new JList();
		JButton backButton = new JButton("Back");
		backButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) { 
				 
				(new StartUILearner()).setVisible(true);
				dispose();
			}
		});
		backButton.setBounds(10, 143, 89, 23);
		contentPane.add(backButton);
		
		
		
		JScrollPane scrollPane = new JScrollPane();
		scrollPane.setBounds(10, 23, 173, 105);
		contentPane.add(scrollPane);
		
		
		
		list.setModel(new AbstractListModel() {
			String[] values = new String[] {"football", "university", "animals", "generations"};
			public int getSize() {
				return values.length;
			}
			public Object getElementAt(int index) {
				return values[index];
			}
		});
		scrollPane.setViewportView(list);
		
		JLabel lblNewLabel = new JLabel("Select an ontology to learn");
		lblNewLabel.setBounds(193, 25, 177, 14);
		contentPane.add(lblNewLabel);
		JButton loadButton = new JButton("Load");
		loadButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) { 
				
				File ontologyFile = new File(ontologies.get(list.getSelectedIndex()));
				(new ExLeInterface(ontologyFile)).setVisible(true);
				dispose();
			}
		});
		loadButton.setEnabled(false);
		loadButton.setBounds(281, 143, 89, 23);
		contentPane.add(loadButton);
		list.addListSelectionListener(new ListSelectionListener() {
			public void valueChanged(ListSelectionEvent arg0) {
				loadButton.setEnabled(true); 
			}
		});
	}

	class startLearning {
		public startLearning(int choice)
		{
			this.actionPerformed(choice);
		}
		public void actionPerformed(int choice) {
			
				System.out.println(ontologyList.getSelectedValue());
				System.out.println(ontologies.get(choice));
				File ontologyFile = new File(ontologies.get(choice));
				(new ExLeInterface(ontologyFile)).setVisible(true);
				setVisible(false);
			
		}
	}
}
