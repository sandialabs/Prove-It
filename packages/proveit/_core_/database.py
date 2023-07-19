import sqlite3

class Database:
    '''
    The Database class uses sqlite3 to maintain a database of
    relations (tables) for a theory package.
    '''

    def __init__(self, db_full_path_name):

        self.name = db_full_path_name.split('/')[-1]
        self.full_name = db_full_path_name

        # connect to (or create) the database
        conn = sqlite3.connect(db_full_path_name)

        # create a cursor
        c = conn.cursor()

        # create our tables/relations,
        # deleting each first if it already exists
        # (The deletions will eventually be omitted, instead using
        # the following code:
        # c.execute("""CREATE TABLE IF NOT EXISTS table_name(...)""")

        c.execute("DROP TABLE IF EXISTS common")
        c.execute("""CREATE TABLE common (
            name       text,
            expression text
            )""")

        c.execute("DROP TABLE IF EXISTS axiom")
        c.execute("""CREATE TABLE axiom (
            name       text,
            expression text
            )""")

        c.execute("DROP TABLE IF EXISTS definition")
        c.execute("""CREATE TABLE definition (
            name       text,
            expression text
            )""")

        c.execute("DROP TABLE IF EXISTS theorem")
        c.execute("""CREATE TABLE theorem (
            name       text,
            expression text,
            proof      text
            )""")

        c.execute("DROP TABLE IF EXISTS proof_step")
        c.execute("""CREATE TABLE proof_step (
            step_id               text,
            step_type             text,
            judgment              text,
            requirements          text,
            equality_requirements text,
            instantiations        text
            )""")

        c.execute("DROP TABLE IF EXISTS judgment")
        c.execute("""CREATE TABLE judgment (
            judgment_id text,
            assumptions text,
            expression  text
            )""")

        c.execute("DROP TABLE IF EXISTS expression")
        c.execute("""CREATE TABLE expression (
            expression_id  text,
            type           text,
            class          text,
            subexpressions text,
            string_format  text,
            latex_format   text
            )""")

        print("Command executed without error!")

        # only five data types!
        # NULL
        # INTEGER
        # REAL
        # TEXT
        # BLOB

        # Commit the commands
        conn.commit()

        # Close the connection
        conn.close()

    def insert_record(self, table, record):
        '''
        Insert a single new record (i.e. row) into the specified table
        in the database. The record must be an appropriate-length
        list of attribute values, else a ValueError is raised.
        '''
        
        print("Entering the insert_record() method.")
        conn = sqlite3.connect(self.full_name)
        c = conn.cursor()

        # An initial minimal check for problems:
        # is the specified table a valid table in the database?
        if table not in self._get_list_of_tables():
            raise ValueError(
                ("Failed attempt to insert a record into the '{0}' table " +
                 "in database '{1}': no such table in the database.").
                format(table, self.name))

        # Another minimal check for problems:
        # length of record must match number of attributes in table.
        # Get the actual number of attributes in the target table.
        c.execute("SELECT count() FROM PRAGMA_TABLE_INFO('{0}')".format(table))
        # Fetch that selected count.
        num_attributes = c.fetchone()[0]
        print("    num_attributes = {}".format(num_attributes))
        if num_attributes != len(record):
            raise ValueError(
                ("Failed attempt to insert a record into the '{0}' table " +
                "in database '{1}'. The provided record had {2} " +
                "attributes, whereas the table expected a record "+
                "with {3} attributes.").format(
                    table, self.name, len(record), num_attributes ))

        # More sophisticated check might eventually be useful as well:
        # check that each attribute value has the correct type (TBA).

        # use num_attributes to construct the correct execution
        # string for inserting the record
        question_mark_string = '('
        for _i in range(num_attributes-1):
            question_mark_string = question_mark_string + '?,'
        question_mark_string = question_mark_string + '?)'

        # Insert attribute values into the specified table
        c.execute("INSERT INTO '{0}' VALUES {1}".
                  format(table, question_mark_string),
                  record)
        print("    Insertion was successful.")

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def delete_record(
            self, table, attribute, attribute_value):
        '''
        Delete one or more records (i.e. one or more rows) from the
        specified table in the database, identifying the records by the
        attribute_value for the given attibute.
        For example, in a table called 'customers', containing
        attributes last_name, first_name, telephone_num, calling the
        following:

            delete_record('customers', 'last_name', 'Brown')

        will delete ALL records with a last_name of 'Brown'.
        The table must be an actual table in the database, and the
        attribute must be an actual attribute of the table, or a
        ValueError is raised.
        Deleting a non-existent record will not raise an error.
        Deletion of a record specified by more than a single attribute
        is not yet supported.
        Note: there is something funky happening with the .format()
        attempt when dealing with a hex value ....
        '''
        print("Entering the delete_record() method.")
        conn = sqlite3.connect(self.full_name)
        c = conn.cursor()

        # An initial minimal check for problems:
        # is the specified table a valid table in the database?
        if table not in self._get_list_of_tables():
            raise ValueError(
                ("Failed attempt to delete a record or records from " +
                 "the '{0}' table in database '{1}': " +
                 "no such table in the database.").
                format(table, self.name))

        # Another minimal check for problems:
        # Does the specified table have the specified attribute?
        if attribute not in self._get_list_of_table_attributes(table):
            raise ValueError(
                ("Failed attempt to delete a record or records from " +
                 "the '{0}' table in database '{1}': " +
                 "no such attribute '{2}' in the table.").
                format(table, self.name, attribute))

        # Delete record(s) from the specified table
        c.execute("DELETE from {0} WHERE {1} = '{2}'".
                  format(table, attribute, attribute_value))
        print("    Deletion raised no fatal errors.")

        # Commit the command(s) and close the connection
        conn.commit()
        conn.close()

    def fetch_all(self, table):
        # Query the db, returning all records in the specified table,
        # in the form of a list of tuples (each tuple corresponding
        # to a record).
        # (Currently a convenience method; to be updated later.)

        # Connect to database
        conn = sqlite3.connect(self.full_name)
        # Create a cursor
        c = conn.cursor()
        # Query the specified table in the database
        c.execute("SELECT rowid, * FROM " + table) # need to fix
        items = c.fetchall()
        # Close our connection
        conn.close
        return items

    # ==================================== #
    # Utility Functions                    #
    # ==================================== #

    def _get_list_of_tables(self):
        '''
        Return a list of the tables in the database.
        This is useful for raising informative errors, for example
        when a client tries to add a record to a non-existent table.
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the table names (an awkward process)
        c.execute("SELECT name from sqlite_master where type='table'")
        temp_list_of_tuples = c.fetchall()
        # temp_list_of_tuples turns out to be a list of
        # single-element tuples, so we clean things up:
        table_names = []
        for item in temp_list_of_tuples:
            table_names.append(item[0])

        # Close connection and return list of table names
        conn.close()
        return list(table_names)

    def _get_list_of_table_attributes(self, table):
        '''
        Return a list of the attributes in the given table.
        This is useful for raising informative errors, for example
        when a client tries to delete a record by specifying a value
        for an attribute that doesn't exist.
        '''

        # Connect to the database.
        conn = sqlite3.connect(self.full_name)
        # Create a cursor
        c = conn.cursor()
        # Obtain the attribute names (an awkward process)
        c.execute("SELECT name FROM PRAGMA_TABLE_INFO('{0}')".
                  format(table));
        temp_list_of_tuples = c.fetchall()
        # temp_list_of_tuples turns out to be a list of
        # single-element tuples, so we clean things up:
        attribute_names = []
        for item in temp_list_of_tuples:
            attribute_names.append(item[0])

        # Close connection and return list of attribute names
        conn.close()
        return list(attribute_names)

